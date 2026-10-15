import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P075_1474D_cleaning_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (old_pre0 : Int) (old_okpre0 : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (old_pre0))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (old_okpre0))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (old_pre0 : Int) (old_okpre0 : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (old_pre0))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (old_okpre0))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (old_okpre0 : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (old_okpre0))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (old_okpre0 : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (old_okpre0))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (1))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ”
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_6_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_6_split_goal_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) ((0 : Int)) ((okpre_values ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) >= (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) (1) ((okpre_values ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) < (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) ((0 : Int)) ((okpre_values ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_suf_terminal : Int) (old_oksuf_terminal : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH7 : (PrefixResidualState values pre_values okpre_values)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> (old_suf_terminal))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (old_oksuf_terminal))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_suf_terminal : Int) (old_oksuf_terminal : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH7 : (PrefixResidualState values pre_values okpre_values)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> (old_suf_terminal))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (old_oksuf_terminal))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_suf_terminal : Int) (old_oksuf_terminal : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH7 : (PrefixResidualState values pre_values okpre_values)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> (old_suf_terminal))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (old_oksuf_terminal))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_oksuf_terminal : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH7 : (PrefixResidualState values pre_values okpre_values)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (old_oksuf_terminal))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_oksuf_terminal : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH7 : (PrefixResidualState values pre_values okpre_values)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (old_oksuf_terminal))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_oksuf_terminal : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH7 : (PrefixResidualState values pre_values okpre_values)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (old_oksuf_terminal))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : (PrefixResidualState values pre_values okpre_values)) (PreH12 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH14 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_22 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values (0 : Int)))) ”
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values (0 : Int)))) ”
)

noncomputable def solver_safety_wit_22_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_22_split_goal_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values (0 : Int)))) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH16 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH17 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH16 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH17 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (suf_leading)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH17 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH18 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_leading : (List Int)) (new_suf_i : Int) (new_oksuf_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH16 : (new_oksuf_i = (0 : Int))) (PreH17 : ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)))) (PreH18 : ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH22 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_leading : (List Int)) (new_suf_i : Int) (new_oksuf_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH16 : (new_oksuf_i = 1)) (PreH17 : ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)))) (PreH18 : ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH22 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values (0 : Int)) = (0 : Int))) (PreH2 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre okpre_values (0 : Int)) = (0 : Int))) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ ((i + 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 2)) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_38 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) ”
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) ”
)

noncomputable def solver_safety_wit_38_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_38_split_goal_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((-9223372036854775808) <= ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "x" ) )) # Int64 |->_)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_44 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |->_)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))))) ”
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |->_)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))))) ”
)

noncomputable def solver_safety_wit_44_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |->_)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_44_split_goal_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |->_)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((-9223372036854775808) <= ((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))))) ”

noncomputable def solver_safety_wit_45 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |-> (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))))))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_46 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH2 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH3 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH4 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH16 : (PrefixResidualState values pre_values okpre_values)) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |-> (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))))))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((i + 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 2)) ”

noncomputable def solver_safety_wit_47 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH2 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH3 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH4 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH16 : (PrefixResidualState values pre_values okpre_values)) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |-> (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))))))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_48 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) = (Znth ((i + 2) - 1) suf_values (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values okpre_values)) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** ((( &( "y" ) )) # Int64 |-> (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))))))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** ((( &( "x" ) )) # Int64 |-> (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_49 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) ≠ (Znth ((i + 2) - 1) suf_values (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values okpre_values)) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_50 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) okpre_values (0 : Int)) = (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_51 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) = (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_52 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) < (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_53 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) < (0 : Int))) (PreH2 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH3 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH4 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH16 : (PrefixResidualState values pre_values okpre_values)) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_54 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "pre" ) )) # Ptr |-> (pre_pre))
  ** ((( &( "suf" ) )) # Ptr |-> (suf_pre))
  ** ((( &( "okpre" ) )) # Ptr |-> (okpre_pre))
  ** ((( &( "oksuf" ) )) # Ptr |-> (oksuf_pre))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX old_okpre0 : Int, EX old_pre0 : Int,
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> (old_pre0))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (old_okpre0))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (1))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = 1) ” &&
  “ ((Zlength (okpre_values)) = 1) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < 1)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) 1 pre_values)
  ** (int64Array.seg_shape pre_pre 1 (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) 1 okpre_values)
  ** (charArray.seg_shape okpre_pre 1 (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (PreH1 : ((0 : Int) <= 9223372036854775807)) (PreH2 : ((0 : Int) >= (-9223372036854775808))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) ,
  (((pre_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape pre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (((okpre_pre + ((0 : Int) * sizeof(CHAR)))) # Char |-> (1))
  ** (charArray.missing_i_shape okpre_pre (0 : Int) (0 : Int) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = 1) ” &&
  “ ((Zlength (okpre_values)) = 1) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < 1)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.seg pre_pre (0 : Int) 1 pre_values)
  ** (int64Array.seg_shape pre_pre 1 (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) 1 okpre_values)
  ** (charArray.seg_shape okpre_pre 1 (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) i pre_values_2)
  ** (int64Array.seg_shape pre_pre i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) i okpre_values_2)
  ** (charArray.seg_shape okpre_pre i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX old_okpre_i : Int, EX old_pre_i : Int, EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) i pre_values)
  ** (((pre_pre + (i * sizeof(INT64)))) # Int64 |-> (old_pre_i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) i okpre_values)
  ** (((okpre_pre + (i * sizeof(CHAR)))) # Char |-> (old_okpre_i))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ”
  &&  (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ”

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ”

noncomputable def solver_entail_wit_3_split_goal_spatial : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth ((i - 1) - (0 : Int)) (okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) ((0 : Int)) ((okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = (i + 1)) ” &&
  “ ((Zlength (okpre_values)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) (i + 1) pre_values)
  ** (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) okpre_values)
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth ((i - 1) - (0 : Int)) (okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) ((0 : Int)) ((okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = (i + 1)) ” &&
  “ ((Zlength (okpre_values)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.seg pre_pre (0 : Int) (i + 1) pre_values)
  ** (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) okpre_values)
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) >= (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) (1) ((okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = (i + 1)) ” &&
  “ ((Zlength (okpre_values)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) (i + 1) pre_values)
  ** (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) okpre_values)
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) >= (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) (1) ((okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = (i + 1)) ” &&
  “ ((Zlength (okpre_values)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.seg pre_pre (0 : Int) (i + 1) pre_values)
  ** (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) okpre_values)
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_entail_wit_4_3 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) < (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) ((0 : Int)) ((okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = (i + 1)) ” &&
  “ ((Zlength (okpre_values)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) (i + 1) pre_values)
  ** (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) okpre_values)
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) < (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH12 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (charArray.full okpre_pre (i + 1) (replace_Znth (i) ((0 : Int)) ((okpre_values_2 ++ (old_okpre_i :: (@List.nil Int))))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values_2 ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values_2 ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (pre_values)) = (i + 1)) ” &&
  “ ((Zlength (okpre_values)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.seg pre_pre (0 : Int) (i + 1) pre_values)
  ** (int64Array.seg_shape pre_pre (i + 1) (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) okpre_values)
  ** (charArray.seg_shape okpre_pre (i + 1) (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) i pre_values_2)
  ** (int64Array.seg_shape pre_pre i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) i okpre_values_2)
  ** (charArray.seg_shape okpre_pre i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  EX old_oksuf_terminal : Int, EX old_suf_terminal : Int, EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> (old_suf_terminal))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (old_oksuf_terminal))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (int64Array.seg pre_pre (0 : Int) i pre_values_2)
  ** (charArray.seg okpre_pre (0 : Int) i okpre_values_2)
|--
  EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
)

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH6 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH7 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH8 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (1))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - n_pre)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - n_pre)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (n_pre + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - n_pre) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - n_pre) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (n_pre + 1))
  ** (int64Array.seg suf_pre (n_pre + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (n_pre + 1))
  ** (charArray.seg oksuf_pre (n_pre + 1) (n_pre + 2) oksuf_values)
) \/
(
forall (oksuf_pre : Int) (suf_pre : Int) (n_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (PreH1 : ((0 : Int) <= 9223372036854775807)) (PreH2 : ((0 : Int) >= (-9223372036854775808))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH9 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH10 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) ,
  (((suf_pre + ((n_pre + 1) * sizeof(INT64)))) # Int64 |-> ((0 : Int)))
  ** (int64Array.missing_i_shape suf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
  ** (((oksuf_pre + ((n_pre + 1) * sizeof(CHAR)))) # Char |-> (1))
  ** (charArray.missing_i_shape oksuf_pre (n_pre + 1) (0 : Int) (n_pre + 2))
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((Zlength (pre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - n_pre)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - n_pre)) ” &&
  “ (PrefixResidualState values pre_values_2 okpre_values_2) ” &&
  “ (SuffixResidualState values (n_pre + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - n_pre) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - n_pre) - q))))) ”
  &&  (int64Array.seg_shape suf_pre (0 : Int) (n_pre + 1))
  ** (int64Array.seg suf_pre (n_pre + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (n_pre + 1))
  ** (charArray.seg oksuf_pre (n_pre + 1) (n_pre + 2) oksuf_values)
)

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i >= 1)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH12 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH13 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH14 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH15 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_prefix : (List Int), EX suf_prefix : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_prefix)) = (i + 1)) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
) \/
(
forall (oksuf_pre : Int) (suf_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (i >= 1)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH12 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH13 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH14 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH15 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
|--
  EX oksuf_prefix : (List Int), EX suf_prefix : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values_2)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_prefix)) = (i + 1)) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values_2 okpre_values_2) ” &&
  “ (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
)

noncomputable def solver_entail_wit_8 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix_2 : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix_2)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH16 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.full suf_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values_2 (0 : Int)))) (suf_prefix)))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix_2)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX new_suf_i : Int, EX oksuf_prefix : (List Int), EX suf_leading : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
) \/
(
forall (suf_pre : Int) (n_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix_2 : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix_2)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH16 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.missing_i suf_pre i (0 : Int) (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values_2 (0 : Int)))) (suf_prefix)))
|--
  EX suf_leading : (List Int),
  “ (((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))) = (Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i + 1) - (i + 1)) suf_values_2 (0 : Int)))) (suf_prefix)) (0 : Int))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values_2)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_prefix_2)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values_2 okpre_values_2) ” &&
  “ (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int)))) ” &&
  “ (((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))) <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.seg suf_pre (0 : Int) i suf_leading)
)

noncomputable def solver_entail_wit_9_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_leading_2 : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i_2 : Int) (i : Int) (PreH1 : ((Znth ((i + 1) - (i + 1)) oksuf_values_2 (0 : Int)) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (suf_leading_2)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH15 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH16 : (new_suf_i_2 = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))))) (PreH17 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i_2)) (PreH18 : (new_suf_i_2 <= (1000000000 * ((n_pre - i) + 1)))) (PreH19 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (charArray.full oksuf_pre (i + 1) (replace_Znth (i) ((0 : Int)) (oksuf_prefix)))
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading_2 ++ (new_suf_i_2 :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
|--
  (EX new_oksuf_i : Int, EX new_suf_i : Int, EX oksuf_leading : (List Int), EX suf_leading : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_leading)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (new_oksuf_i = (0 : Int)) ” &&
  “ ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i))) ” &&
  “ ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1)) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values))
  ||
  (EX new_oksuf_i : Int, EX new_suf_i : Int, EX oksuf_leading : (List Int), EX suf_leading : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_leading)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (new_oksuf_i = 1) ” &&
  “ ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i))) ” &&
  “ ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1)) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values))

noncomputable def solver_entail_wit_9_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_leading_2 : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i_2 : Int) (i : Int) (PreH1 : ((Znth (i - (0 : Int)) (suf_leading_2 ++ (new_suf_i_2 :: (@List.nil Int))) (0 : Int)) >= (0 : Int))) (PreH2 : ((Znth ((i + 1) - (i + 1)) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (suf_leading_2)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH16 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH17 : (new_suf_i_2 = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))))) (PreH18 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i_2)) (PreH19 : (new_suf_i_2 <= (1000000000 * ((n_pre - i) + 1)))) (PreH20 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH21 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (charArray.full oksuf_pre (i + 1) (replace_Znth (i) (1) (oksuf_prefix)))
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading_2 ++ (new_suf_i_2 :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
|--
  (EX new_oksuf_i : Int, EX new_suf_i : Int, EX oksuf_leading : (List Int), EX suf_leading : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_leading)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (new_oksuf_i = (0 : Int)) ” &&
  “ ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i))) ” &&
  “ ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1)) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values))
  ||
  (EX new_oksuf_i : Int, EX new_suf_i : Int, EX oksuf_leading : (List Int), EX suf_leading : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_leading)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (new_oksuf_i = 1) ” &&
  “ ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i))) ” &&
  “ ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1)) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values))

noncomputable def solver_entail_wit_9_3 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_leading_2 : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i_2 : Int) (i : Int) (PreH1 : ((Znth (i - (0 : Int)) (suf_leading_2 ++ (new_suf_i_2 :: (@List.nil Int))) (0 : Int)) < (0 : Int))) (PreH2 : ((Znth ((i + 1) - (i + 1)) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (suf_leading_2)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH16 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH17 : (new_suf_i_2 = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))))) (PreH18 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i_2)) (PreH19 : (new_suf_i_2 <= (1000000000 * ((n_pre - i) + 1)))) (PreH20 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH21 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (charArray.full oksuf_pre (i + 1) (replace_Znth (i) ((0 : Int)) (oksuf_prefix)))
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading_2 ++ (new_suf_i_2 :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
|--
  (EX new_oksuf_i : Int, EX new_suf_i : Int, EX oksuf_leading : (List Int), EX suf_leading : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_leading)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (new_oksuf_i = (0 : Int)) ” &&
  “ ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i))) ” &&
  “ ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1)) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values))
  ||
  (EX new_oksuf_i : Int, EX new_suf_i : Int, EX oksuf_leading : (List Int), EX suf_leading : (List Int), EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_leading)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (new_oksuf_i = 1) ” &&
  “ ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i))) ” &&
  “ ((((Znth (0 : Int) oksuf_values (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1)) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values))

noncomputable def solver_entail_wit_10_1 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_leading : (List Int)) (oksuf_leading : (List Int)) (new_suf_i : Int) (new_oksuf_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH15 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))))) (PreH16 : (new_oksuf_i = (0 : Int))) (PreH17 : ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)))) (PreH18 : ((((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH21 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH22 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values ((i - 1) + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1)) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - (i - 1)) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) ((i - 1) + 1))
  ** (int64Array.seg suf_pre ((i - 1) + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) ((i - 1) + 1))
  ** (charArray.seg oksuf_pre ((i - 1) + 1) (n_pre + 2) oksuf_values)
) \/
(
forall (oksuf_pre : Int) (suf_pre : Int) (n_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_leading : (List Int)) (oksuf_leading : (List Int)) (new_suf_i : Int) (new_oksuf_i : Int) (i : Int) (PreH1 : (new_suf_i <= 9223372036854775807)) (PreH2 : (new_suf_i >= (-9223372036854775808))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_leading)) = i)) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH16 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH17 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))))) (PreH18 : (new_oksuf_i = (0 : Int))) (PreH19 : ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)))) (PreH20 : ((((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH21 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH22 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH23 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH24 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((Zlength (pre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ (PrefixResidualState values pre_values_2 okpre_values_2) ” &&
  “ (SuffixResidualState values ((i - 1) + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1)) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - (i - 1)) - q))))) ”
  &&  (int64Array.seg_shape suf_pre (0 : Int) ((i - 1) + 1))
  ** (int64Array.seg suf_pre ((i - 1) + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) ((i - 1) + 1))
  ** (charArray.seg oksuf_pre ((i - 1) + 1) (n_pre + 2) oksuf_values)
)

noncomputable def solver_entail_wit_10_2 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_leading : (List Int)) (oksuf_leading : (List Int)) (new_suf_i : Int) (new_oksuf_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH15 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))))) (PreH16 : (new_oksuf_i = 1)) (PreH17 : ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)))) (PreH18 : ((((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH21 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH22 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values ((i - 1) + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1)) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - (i - 1)) - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) ((i - 1) + 1))
  ** (int64Array.seg suf_pre ((i - 1) + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) ((i - 1) + 1))
  ** (charArray.seg oksuf_pre ((i - 1) + 1) (n_pre + 2) oksuf_values)
) \/
(
forall (oksuf_pre : Int) (suf_pre : Int) (n_pre : Int) (values : (List Int)) (pre_values_2 : (List Int)) (okpre_values_2 : (List Int)) (suf_values_2 : (List Int)) (oksuf_values_2 : (List Int)) (suf_leading : (List Int)) (oksuf_leading : (List Int)) (new_suf_i : Int) (new_oksuf_i : Int) (i : Int) (PreH1 : (new_suf_i <= 9223372036854775807)) (PreH2 : (new_suf_i >= (-9223372036854775808))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_leading)) = i)) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH16 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH17 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values_2 (0 : Int))))) (PreH18 : (new_oksuf_i = 1)) (PreH19 : ((new_oksuf_i = 1) -> (((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)))) (PreH20 : ((((Znth (0 : Int) oksuf_values_2 (0 : Int)) = 1) ∧ ((0 : Int) <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH21 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH22 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH23 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH24 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.seg oksuf_pre (0 : Int) i oksuf_leading)
  ** (((oksuf_pre + (i * sizeof(CHAR)))) # Char |-> (new_oksuf_i))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((Zlength (pre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - (i - 1))) ” &&
  “ (PrefixResidualState values pre_values_2 okpre_values_2) ” &&
  “ (SuffixResidualState values ((i - 1) + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1)) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - (i - 1)) - q))))) ”
  &&  (int64Array.seg_shape suf_pre (0 : Int) ((i - 1) + 1))
  ** (int64Array.seg suf_pre ((i - 1) + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) ((i - 1) + 1))
  ** (charArray.seg oksuf_pre ((i - 1) + 1) (n_pre + 2) oksuf_values)
)

noncomputable def solver_entail_wit_11_1 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth n_pre okpre_values_2 (0 : Int)) = (0 : Int))) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH16 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
) \/
(
forall (oksuf_pre : Int) (suf_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth n_pre okpre_values_2 (0 : Int)) = (0 : Int))) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH15 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH16 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (pre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values_2 okpre_values_2) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values_2 suf_values okpre_values_2 oksuf_values 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
)

noncomputable def solver_entail_wit_11_2 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth n_pre okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH15 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH17 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
) \/
(
forall (oksuf_pre : Int) (suf_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth n_pre okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values_2)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values_2)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH15 : (SuffixResidualState values (i + 1) suf_values_2 oksuf_values_2)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> ((((-1000000000) * k_4) <= (Znth k_4 pre_values_2 (0 : Int))) ∧ ((Znth k_4 pre_values_2 (0 : Int)) <= (1000000000 * k_4))))) (PreH17 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i) - q_2)) <= (Znth q_2 suf_values_2 (0 : Int))) ∧ ((Znth q_2 suf_values_2 (0 : Int)) <= (1000000000 * ((n_pre - i) - q_2)))))) ,
  (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (pre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values_2)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values_2 okpre_values_2) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values_2 suf_values okpre_values_2 oksuf_values 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
)

noncomputable def solver_entail_wit_12_1 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) ≠ (Znth ((i + 2) - 1) suf_values_2 (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH18 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH19 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
) \/
(
forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) ≠ (Znth ((i + 2) - 1) suf_values_2 (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH18 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH19 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) ≠ (Znth ((i + 2) - 1) suf_values_2 (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH18 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH19 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1))

noncomputable def solver_entail_wit_12_2 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) okpre_values_2 (0 : Int)) = (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH15 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values_2)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values_2)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
) \/
(
forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) okpre_values_2 (0 : Int)) = (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH15 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) okpre_values_2 (0 : Int)) = (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH14 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH15 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1))

noncomputable def solver_entail_wit_12_3 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) = (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH15 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH16 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values_2)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
) \/
(
forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) = (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH15 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH16 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) = (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH15 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH16 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1))

noncomputable def solver_entail_wit_12_4 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) < (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH16 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH17 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values_2)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
) \/
(
forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) < (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH16 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH17 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) < (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH16 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH17 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1))

noncomputable def solver_entail_wit_12_5 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) < (0 : Int))) (PreH2 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) >= (0 : Int))) (PreH3 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH4 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH15 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH16 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH17 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH18 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values_2)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values_2)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values_2)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values_2)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  EX oksuf_values : (List Int), EX suf_values : (List Int), EX okpre_values : (List Int), EX pre_values : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
) \/
(
forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) < (0 : Int))) (PreH2 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) >= (0 : Int))) (PreH3 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH4 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH15 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH16 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH17 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH18 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (values : (List Int)) (oksuf_values_2 : (List Int)) (suf_values_2 : (List Int)) (okpre_values_2 : (List Int)) (pre_values_2 : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int)))) < (0 : Int))) (PreH2 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values_2 (0 : Int))) >= (0 : Int))) (PreH3 : ((Znth ((i + 2) - 1) oksuf_values_2 (0 : Int)) ≠ (0 : Int))) (PreH4 : ((Znth (i - 1) okpre_values_2 (0 : Int)) ≠ (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (n_pre + 1))) (PreH13 : ((Zlength (okpre_values_2)) = (n_pre + 1))) (PreH14 : ((Zlength (suf_values_2)) = (n_pre + 1))) (PreH15 : ((Zlength (oksuf_values_2)) = (n_pre + 1))) (PreH16 : (PrefixResidualState values pre_values_2 okpre_values_2)) (PreH17 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2)) (PreH18 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values_2 (0 : Int))) ∧ ((Znth k_2 pre_values_2 (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values_2 (0 : Int))) ∧ ((Znth q suf_values_2 (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ (Spec values (0 : Int)) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ (Spec values (0 : Int)) ”
  &&  (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ (Spec values (0 : Int)) ”

noncomputable def solver_return_wit_1_split_goal_spatial : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) = (Znth ((i + 2) - 1) suf_values (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values okpre_values)) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (Spec values 1) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) = (Znth ((i + 2) - 1) suf_values (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values okpre_values)) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (Spec values 1) ”
  &&  (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) = (Znth ((i + 2) - 1) suf_values (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values okpre_values)) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (Spec values 1) ”

noncomputable def solver_return_wit_2_split_goal_spatial : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) = (Znth ((i + 2) - 1) suf_values (0 : Int)))) (PreH2 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH3 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH4 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH5 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH17 : (PrefixResidualState values pre_values okpre_values)) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values (0 : Int)) = (0 : Int))) (PreH2 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (Spec values 1) ”
  &&  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
) \/
(
forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values (0 : Int)) = (0 : Int))) (PreH2 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (Spec values 1) ”
  &&  (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
)

noncomputable def solver_return_wit_3_split_goal_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values (0 : Int)) = (0 : Int))) (PreH2 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (Spec values 1) ”

noncomputable def solver_return_wit_3_split_goal_spatial : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre pre_values (0 : Int)) = (0 : Int))) (PreH2 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  (int64Array.full_shape pre_pre (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.full_shape okpre_pre (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) i pre_values)
  ** (((pre_pre + (i * sizeof(INT64)))) # Int64 |-> (old_pre_i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) i okpre_values)
  ** (((okpre_pre + (i * sizeof(CHAR)))) # Char |-> (old_okpre_i))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64 |-> ((Znth i ((0 : Int) :: values) (0 : Int))))
  ** (int64Array.missing_i a_pre i (0 : Int) (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg pre_pre (0 : Int) i pre_values)
  ** (((pre_pre + (i * sizeof(INT64)))) # Int64 |-> (old_pre_i))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.seg okpre_pre (0 : Int) i okpre_values)
  ** (((okpre_pre + (i * sizeof(CHAR)))) # Char |-> (old_okpre_i))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((pre_pre + ((i - 1) * sizeof(INT64)))) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int))))
  ** (int64Array.missing_i pre_pre (i - 1) (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.seg pre_pre (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.missing_i pre_pre i (0 : Int) (i + 1) (pre_values ++ (old_pre_i :: (@List.nil Int))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((okpre_pre + ((i - 1) * sizeof(CHAR)))) # Char |-> ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i okpre_pre (i - 1) (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64 |-> ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))) (0 : Int))))
  ** (int64Array.missing_i pre_pre i (0 : Int) (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((okpre_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i okpre_pre i (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) >= (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) >= (0 : Int)) ” &&
  “ ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((okpre_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i okpre_pre i (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (old_pre_i : Int) (old_okpre_i : Int) (i : Int) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) < (0 : Int))) (PreH2 : ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values)) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) ,
  (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (charArray.seg okpre_pre (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))
|--
  “ ((Znth i (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))) (0 : Int)) < (0 : Int)) ” &&
  “ ((Znth ((i - 1) - (0 : Int)) (okpre_values ++ (old_okpre_i :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = i) ” &&
  “ ((Zlength (okpre_values)) = i) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ”
  &&  (((okpre_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i okpre_pre i (0 : Int) (i + 1) (okpre_values ++ (old_okpre_i :: (@List.nil Int))))
  ** (int64Array.full pre_pre (i + 1) (replace_Znth (i) (((Znth i ((0 : Int) :: values) (0 : Int)) - (Znth ((i - 1) - (0 : Int)) (pre_values ++ (old_pre_i :: (@List.nil Int))) (0 : Int)))) ((pre_values ++ (old_pre_i :: (@List.nil Int))))))
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.missing_i_shape pre_pre i i (n_pre + 1))
  ** (int64Array.full_shape suf_pre (n_pre + 2))
  ** (charArray.missing_i_shape okpre_pre i i (n_pre + 1))
  ** (charArray.full_shape oksuf_pre (n_pre + 2))

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_prefix)) = (i + 1)) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64 |-> ((Znth i ((0 : Int) :: values) (0 : Int))))
  ** (int64Array.missing_i a_pre i (0 : Int) (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_prefix)) = (i + 1)) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((suf_pre + ((i + 1) * sizeof(INT64)))) # Int64 |-> ((Znth ((i + 1) - (i + 1)) suf_values (0 : Int))))
  ** (int64Array.missing_i suf_pre (i + 1) (i + 1) (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_prefix : (List Int)) (oksuf_prefix : (List Int)) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) suf_prefix)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_prefix)) = (i + 1)) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((suf_pre + (i * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.missing_i suf_pre i (0 : Int) (i + 1) suf_prefix)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH16 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH17 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((oksuf_pre + ((i + 1) * sizeof(CHAR)))) # Char |-> ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int))))
  ** (charArray.missing_i oksuf_pre (i + 1) (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (0 : Int) i suf_leading)
  ** (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> (new_suf_i))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (suf_leading)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH17 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH18 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
|--
  “ ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((suf_pre + (i * sizeof(INT64)))) # Int64 |-> ((Znth (i - (0 : Int)) (suf_leading ++ (new_suf_i :: (@List.nil Int))) (0 : Int))))
  ** (int64Array.missing_i suf_pre i (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (suf_leading)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH16 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH17 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH18 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
|--
  “ ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((oksuf_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i oksuf_pre i (0 : Int) (i + 1) oksuf_prefix)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)

noncomputable def solver_partial_solve_wit_15 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : ((Znth (i - (0 : Int)) (suf_leading ++ (new_suf_i :: (@List.nil Int))) (0 : Int)) >= (0 : Int))) (PreH2 : ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH17 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH18 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH19 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
|--
  “ ((Znth (i - (0 : Int)) (suf_leading ++ (new_suf_i :: (@List.nil Int))) (0 : Int)) >= (0 : Int)) ” &&
  “ ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((oksuf_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i oksuf_pre i (0 : Int) (i + 1) oksuf_prefix)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (pre_values : (List Int)) (okpre_values : (List Int)) (suf_values : (List Int)) (oksuf_values : (List Int)) (suf_leading : (List Int)) (oksuf_prefix : (List Int)) (new_suf_i : Int) (i : Int) (PreH1 : ((Znth (i - (0 : Int)) (suf_leading ++ (new_suf_i :: (@List.nil Int))) (0 : Int)) < (0 : Int))) (PreH2 : ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH17 : (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int))))) (PreH18 : (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i)) (PreH19 : (new_suf_i <= (1000000000 * ((n_pre - i) + 1)))) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg oksuf_pre (0 : Int) (i + 1) oksuf_prefix)
|--
  “ ((Znth (i - (0 : Int)) (suf_leading ++ (new_suf_i :: (@List.nil Int))) (0 : Int)) < (0 : Int)) ” &&
  “ ((Znth ((i + 1) - (i + 1)) oksuf_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (suf_leading)) = i) ” &&
  “ ((Zlength (oksuf_prefix)) = (i + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ (new_suf_i = ((Znth (i - 1) values (0 : Int)) - (Znth (0 : Int) suf_values (0 : Int)))) ” &&
  “ (((-1000000000) * ((n_pre - i) + 1)) <= new_suf_i) ” &&
  “ (new_suf_i <= (1000000000 * ((n_pre - i) + 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((oksuf_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i oksuf_pre i (0 : Int) (i + 1) oksuf_prefix)
  ** (int64Array.seg suf_pre (0 : Int) (i + 1) (suf_leading ++ (new_suf_i :: (@List.nil Int))))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)

noncomputable def solver_partial_solve_wit_17 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i < 1)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH14 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH15 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ (i < 1) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((okpre_pre + (n_pre * sizeof(CHAR)))) # Char |-> ((Znth n_pre okpre_values (0 : Int))))
  ** (charArray.missing_i okpre_pre n_pre (0 : Int) (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)

noncomputable def solver_partial_solve_wit_18 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int))) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1) - i))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1) - i))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values (i + 1) suf_values oksuf_values)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q)))))) ,
  (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)
|--
  “ ((Znth n_pre okpre_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < 1) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = ((n_pre + 1) - i)) ” &&
  “ ((Zlength (oksuf_values)) = ((n_pre + 1) - i)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values (i + 1) suf_values oksuf_values) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i) - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * ((n_pre - i) - q))))) ”
  &&  (((pre_pre + (n_pre * sizeof(INT64)))) # Int64 |-> ((Znth n_pre pre_values (0 : Int))))
  ** (int64Array.missing_i pre_pre n_pre (0 : Int) (n_pre + 1) pre_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.seg_shape suf_pre (0 : Int) (i + 1))
  ** (int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) (i + 1))
  ** (charArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values)

noncomputable def solver_partial_solve_wit_19 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH12 : (PrefixResidualState values pre_values okpre_values)) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH15 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH16 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (((okpre_pre + ((i - 1) * sizeof(CHAR)))) # Char |-> ((Znth (i - 1) okpre_values (0 : Int))))
  ** (charArray.missing_i okpre_pre (i - 1) (0 : Int) (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)

noncomputable def solver_partial_solve_wit_20 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH13 : (PrefixResidualState values pre_values okpre_values)) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH17 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
|--
  “ ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (((oksuf_pre + ((i + 2) * sizeof(CHAR)))) # Char |-> ((Znth ((i + 2) - 1) oksuf_values (0 : Int))))
  ** (charArray.missing_i oksuf_pre (i + 2) 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)

noncomputable def solver_partial_solve_wit_21 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (((a_pre + ((i + 1) * sizeof(INT64)))) # Int64 |-> ((Znth (i + 1) ((0 : Int) :: values) (0 : Int))))
  ** (int64Array.missing_i a_pre (i + 1) (0 : Int) (n_pre + 1) ((0 : Int) :: values))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)

noncomputable def solver_partial_solve_wit_22 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH14 : (PrefixResidualState values pre_values okpre_values)) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH18 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (((pre_pre + ((i - 1) * sizeof(INT64)))) # Int64 |-> ((Znth (i - 1) pre_values (0 : Int))))
  ** (int64Array.missing_i pre_pre (i - 1) (0 : Int) (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)

noncomputable def solver_partial_solve_wit_23 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH2 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH3 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH15 : (PrefixResidualState values pre_values okpre_values)) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int)) ” &&
  “ ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64 |-> ((Znth i ((0 : Int) :: values) (0 : Int))))
  ** (int64Array.missing_i a_pre i (0 : Int) (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)

noncomputable def solver_partial_solve_wit_24 : Prop :=
  forall (oksuf_pre : Int) (okpre_pre : Int) (suf_pre : Int) (pre_pre : Int) (n_pre : Int) (a_pre : Int) (values : (List Int)) (oksuf_values : (List Int)) (suf_values : (List Int)) (okpre_values : (List Int)) (pre_values : (List Int)) (i : Int) (PreH1 : (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int))) (PreH2 : (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int))) (PreH3 : ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int))) (PreH4 : ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1))) (PreH16 : (PrefixResidualState values pre_values okpre_values)) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values)) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i)) (PreH19 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2))))) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q)))))) ,
  (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (int64Array.seg suf_pre 1 (n_pre + 2) suf_values)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)
|--
  “ (((Znth i ((0 : Int) :: values) (0 : Int)) - ((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int)))) >= (0 : Int)) ” &&
  “ (((Znth (i + 1) ((0 : Int) :: values) (0 : Int)) - (Znth (i - 1) pre_values (0 : Int))) >= (0 : Int)) ” &&
  “ ((Znth ((i + 2) - 1) oksuf_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((Znth (i - 1) okpre_values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (pre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (okpre_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (suf_values)) = (n_pre + 1)) ” &&
  “ ((Zlength (oksuf_values)) = (n_pre + 1)) ” &&
  “ (PrefixResidualState values pre_values okpre_values) ” &&
  “ (SuffixResidualState values 1 suf_values oksuf_values) ” &&
  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> ((((-1000000000) * k_2) <= (Znth k_2 pre_values (0 : Int))) ∧ ((Znth k_2 pre_values (0 : Int)) <= (1000000000 * k_2)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q)) <= (Znth q suf_values (0 : Int))) ∧ ((Znth q suf_values (0 : Int)) <= (1000000000 * (n_pre - q))))) ”
  &&  (((suf_pre + ((i + 2) * sizeof(INT64)))) # Int64 |-> ((Znth ((i + 2) - 1) suf_values (0 : Int))))
  ** (int64Array.missing_i suf_pre (i + 2) 1 (n_pre + 2) suf_values)
  ** (int64Array.full a_pre (n_pre + 1) ((0 : Int) :: values))
  ** (int64Array.full pre_pre (n_pre + 1) pre_values)
  ** (charArray.seg oksuf_pre 1 (n_pre + 2) oksuf_values)
  ** (charArray.full okpre_pre (n_pre + 1) okpre_values)
  ** (int64Array.seg_shape suf_pre (0 : Int) 1)
  ** (charArray.seg_shape oksuf_pre (0 : Int) 1)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
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
  proof_of_solver_safety_wit_35 : solver_safety_wit_35
  proof_of_solver_safety_wit_36 : solver_safety_wit_36
  proof_of_solver_safety_wit_37 : solver_safety_wit_37
  proof_of_solver_safety_wit_39 : solver_safety_wit_39
  proof_of_solver_safety_wit_40 : solver_safety_wit_40
  proof_of_solver_safety_wit_41 : solver_safety_wit_41
  proof_of_solver_safety_wit_42 : solver_safety_wit_42
  proof_of_solver_safety_wit_43 : solver_safety_wit_43
  proof_of_solver_safety_wit_45 : solver_safety_wit_45
  proof_of_solver_safety_wit_46 : solver_safety_wit_46
  proof_of_solver_safety_wit_47 : solver_safety_wit_47
  proof_of_solver_safety_wit_48 : solver_safety_wit_48
  proof_of_solver_safety_wit_49 : solver_safety_wit_49
  proof_of_solver_safety_wit_50 : solver_safety_wit_50
  proof_of_solver_safety_wit_51 : solver_safety_wit_51
  proof_of_solver_safety_wit_52 : solver_safety_wit_52
  proof_of_solver_safety_wit_53 : solver_safety_wit_53
  proof_of_solver_safety_wit_54 : solver_safety_wit_54
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
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
  proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13
  proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17
  proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18
  proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19
  proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20
  proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21
  proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22
  proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23
  proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_22 : solver_safety_wit_22
  proof_of_solver_safety_wit_38 : solver_safety_wit_38
  proof_of_solver_safety_wit_44 : solver_safety_wit_44
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_entail_wit_8 : solver_entail_wit_8
  proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1
  proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2
  proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3
  proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1
  proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2
  proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1
  proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2
  proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1
  proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2
  proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3
  proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4
  proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_goal
