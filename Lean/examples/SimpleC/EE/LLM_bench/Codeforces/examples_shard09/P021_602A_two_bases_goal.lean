import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P021_602A_two_bases_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def numeral_value_safety_wit_1 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) ,
  ((( &( "v" ) )) # Int64 |->_)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** (intArray.full d_pre n_pre digits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def numeral_value_safety_wit_2 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** (intArray.full d_pre n_pre digits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def numeral_value_safety_wit_3 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (((v * b_pre) + (Znth i digits (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def numeral_value_safety_wit_4 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
|--
  “ (((v * b_pre) + (Znth i digits (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((v * b_pre) + (Znth i digits (0 : Int)))) ”
) \/
(
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
|--
  “ (((v * b_pre) + (Znth i digits (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((v * b_pre) + (Znth i digits (0 : Int)))) ”
)

noncomputable def numeral_value_safety_wit_4_split_goal_1 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
|--
  “ (((v * b_pre) + (Znth i digits (0 : Int))) <= 9223372036854775807) ”

noncomputable def numeral_value_safety_wit_4_split_goal_2 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
|--
  “ ((-9223372036854775808) <= ((v * b_pre) + (Znth i digits (0 : Int)))) ”

noncomputable def numeral_value_safety_wit_5 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
  ** (intArray.full d_pre n_pre digits)
|--
  “ ((v * b_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (v * b_pre)) ”
) \/
(
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
  ** (intArray.full d_pre n_pre digits)
|--
  “ ((v * b_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (v * b_pre)) ”
)

noncomputable def numeral_value_safety_wit_5_split_goal_1 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
  ** (intArray.full d_pre n_pre digits)
|--
  “ ((v * b_pre) <= 9223372036854775807) ”

noncomputable def numeral_value_safety_wit_5_split_goal_2 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "v" ) )) # Int64 |-> (v))
  ** (intArray.full d_pre n_pre digits)
|--
  “ ((-9223372036854775808) <= (v * b_pre)) ”

noncomputable def numeral_value_entail_wit_1 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 digits (0 : Int))) ∧ ((Znth k_2 digits (0 : Int)) < b_pre)))) ,
  (intArray.full d_pre n_pre digits)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 10) ” &&
  “ (2 <= b_pre) ” &&
  “ (b_pre <= 40) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) = (numeral (b_pre) ((sublist ((0 : Int)) ((0 : Int)) (digits))))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((Z.pow (40) ((0 : Int))) - 1)) ”
  &&  (intArray.full d_pre n_pre digits)
) \/
(
forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 digits (0 : Int))) ∧ ((Znth k_2 digits (0 : Int)) < b_pre)))) ,
  TT && emp 
|--
  “ ((0 : Int) <= ((Z.pow (40) ((0 : Int))) - 1)) ” &&
  “ ((0 : Int) = (numeral (b_pre) ((sublist ((0 : Int)) ((0 : Int)) (digits))))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre))) ”
  &&  emp
)

noncomputable def numeral_value_entail_wit_1_split_goal_1 : Prop :=
  forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 digits (0 : Int))) ∧ ((Znth k_2 digits (0 : Int)) < b_pre)))) ,
  ((0 : Int) <= ((Z.pow (40) ((0 : Int))) - 1))

noncomputable def numeral_value_entail_wit_1_split_goal_2 : Prop :=
  forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 digits (0 : Int))) ∧ ((Znth k_2 digits (0 : Int)) < b_pre)))) ,
  ((0 : Int) = (numeral (b_pre) ((sublist ((0 : Int)) ((0 : Int)) (digits)))))

noncomputable def numeral_value_entail_wit_1_split_goal_3 : Prop :=
  forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 digits (0 : Int))) ∧ ((Znth k_2 digits (0 : Int)) < b_pre)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))

noncomputable def numeral_value_entail_wit_2 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 10) ” &&
  “ (2 <= b_pre) ” &&
  “ (b_pre <= 40) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (((v * b_pre) + (Znth i digits (0 : Int))) = (numeral (b_pre) ((sublist ((0 : Int)) ((i + 1)) (digits))))) ” &&
  “ ((0 : Int) <= ((v * b_pre) + (Znth i digits (0 : Int)))) ” &&
  “ (((v * b_pre) + (Znth i digits (0 : Int))) <= ((Z.pow (40) ((i + 1))) - 1)) ”
  &&  (intArray.full d_pre n_pre digits)
) \/
(
forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  TT && emp 
|--
  “ (((v * b_pre) + (Znth i digits (0 : Int))) <= ((Z.pow (40) ((i + 1))) - 1)) ” &&
  “ (((v * b_pre) + (Znth i digits (0 : Int))) = (numeral (b_pre) ((sublist ((0 : Int)) ((i + 1)) (digits))))) ”
  &&  emp
)

noncomputable def numeral_value_entail_wit_2_split_goal_1 : Prop :=
  forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (((v * b_pre) + (Znth i digits (0 : Int))) <= ((Z.pow (40) ((i + 1))) - 1))

noncomputable def numeral_value_entail_wit_2_split_goal_2 : Prop :=
  forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (((v * b_pre) + (Znth i digits (0 : Int))) = (numeral (b_pre) ((sublist ((0 : Int)) ((i + 1)) (digits)))))

noncomputable def numeral_value_return_wit_1 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
|--
  “ (v = (numeral (b_pre) (digits))) ”
  &&  (intArray.full d_pre n_pre digits)
) \/
(
forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  TT && emp 
|--
  “ (v = (numeral (b_pre) (digits))) ”
  &&  emp
)

noncomputable def numeral_value_return_wit_1_split_goal_1 : Prop :=
  forall (digits : (List Int)) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (v = (numeral (b_pre) (digits)))

noncomputable def numeral_value_partial_solve_wit_1 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (b_pre : Int) (v : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits)))))) (PreH11 : ((0 : Int) <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1))) ,
  (intArray.full d_pre n_pre digits)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 10) ” &&
  “ (2 <= b_pre) ” &&
  “ (b_pre <= 40) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k digits (0 : Int))) ∧ ((Znth k digits (0 : Int)) < b_pre))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (v = (numeral (b_pre) ((sublist ((0 : Int)) (i) (digits))))) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= ((Z.pow (40) (i)) - 1)) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int |-> ((Znth i digits (0 : Int))))
  ** (intArray.missing_i d_pre i (0 : Int) n_pre digits)

noncomputable def solver_safety_wit_1 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full y_pre m_pre y_digits)
  ** ((( &( "vy" ) )) # Int64 |-> (retval_2))
  ** (intArray.full x_pre n_pre x_digits)
  ** ((( &( "vx" ) )) # Int64 |-> (retval))
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
|--
  “ (60 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 60) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full y_pre m_pre y_digits)
  ** ((( &( "vy" ) )) # Int64 |-> (retval_2))
  ** (intArray.full x_pre n_pre x_digits)
  ** ((( &( "vx" ) )) # Int64 |-> (retval))
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
|--
  “ (62 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 62) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full y_pre m_pre y_digits)
  ** ((( &( "vy" ) )) # Int64 |-> (retval_2))
  ** (intArray.full x_pre n_pre x_digits)
  ** ((( &( "vx" ) )) # Int64 |-> (retval))
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
|--
  “ (61 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 61) ”

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full y_pre m_pre y_digits)
  ** (intArray.full x_pre n_pre x_digits)
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 60) ”
  &&  (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
) \/
(
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (n_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))) ,
  TT && emp 
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 60) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (n_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))) ,
  (Spec bx_pre basey_pre x_digits y_digits 60)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full y_pre m_pre y_digits)
  ** (intArray.full x_pre n_pre x_digits)
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 62) ”
  &&  (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
) \/
(
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (n_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  TT && emp 
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 62) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (n_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  (Spec bx_pre basey_pre x_digits y_digits 62)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full y_pre m_pre y_digits)
  ** (intArray.full x_pre n_pre x_digits)
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 61) ”
  &&  (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
) \/
(
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (n_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  TT && emp 
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 61) ”
  &&  emp
)

noncomputable def solver_return_wit_3_split_goal_1 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (n_pre : Int) (m_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH14 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))) ,
  (Spec bx_pre basey_pre x_digits y_digits 61)

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  (
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 10)) (PreH5 : (2 <= bx_pre)) (PreH6 : (bx_pre <= 40)) (PreH7 : (2 <= basey_pre)) (PreH8 : (basey_pre <= 40)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH10 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH11 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH12 : (n_pre = (Zlength (x_digits)))) (PreH13 : (m_pre = (Zlength (y_digits)))) ,
  ((( &( "vx" ) )) # Int64 |->_)
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 10) ” &&
  “ (2 <= bx_pre) ” &&
  “ (bx_pre <= 40) ” &&
  “ (n_pre = (Zlength (x_digits))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k x_digits (0 : Int))) ∧ ((Znth k x_digits (0 : Int)) < bx_pre))) ”
) \/
(
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (PreH1 : (m_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (basey_pre <= INT_MAX)) (PreH4 : (bx_pre <= INT_MAX)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (basey_pre >= INT_MIN)) (PreH8 : (bx_pre >= INT_MIN)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 10)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10)) (PreH13 : (2 <= bx_pre)) (PreH14 : (bx_pre <= 40)) (PreH15 : (2 <= basey_pre)) (PreH16 : (basey_pre <= 40)) (PreH17 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH18 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH19 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH20 : (n_pre = (Zlength (x_digits)))) (PreH21 : (m_pre = (Zlength (y_digits)))) ,
  ((( &( "vx" ) )) # Int64 |->_)
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k x_digits (0 : Int))) ∧ ((Znth k x_digits (0 : Int)) < bx_pre))) ”
)

noncomputable def solver_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (PreH1 : (m_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (basey_pre <= INT_MAX)) (PreH4 : (bx_pre <= INT_MAX)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (basey_pre >= INT_MIN)) (PreH8 : (bx_pre >= INT_MIN)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 10)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10)) (PreH13 : (2 <= bx_pre)) (PreH14 : (bx_pre <= 40)) (PreH15 : (2 <= basey_pre)) (PreH16 : (basey_pre <= 40)) (PreH17 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH18 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH19 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH20 : (n_pre = (Zlength (x_digits)))) (PreH21 : (m_pre = (Zlength (y_digits)))) ,
  ((( &( "vx" ) )) # Int64 |->_)
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k x_digits (0 : Int))) ∧ ((Znth k x_digits (0 : Int)) < bx_pre))) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 10)) (PreH5 : (2 <= bx_pre)) (PreH6 : (bx_pre <= 40)) (PreH7 : (2 <= basey_pre)) (PreH8 : (basey_pre <= 40)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH10 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH11 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH12 : (n_pre = (Zlength (x_digits)))) (PreH13 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 10) ” &&
  “ (2 <= bx_pre) ” &&
  “ (bx_pre <= 40) ” &&
  “ (n_pre = (Zlength (x_digits))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k x_digits (0 : Int))) ∧ ((Znth k x_digits (0 : Int)) < bx_pre))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 10) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 10) ” &&
  “ (2 <= bx_pre) ” &&
  “ (bx_pre <= 40) ” &&
  “ (2 <= basey_pre) ” &&
  “ (basey_pre <= 40) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre))) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre))) ” &&
  “ (Pre bx_pre basey_pre x_digits y_digits) ” &&
  “ (n_pre = (Zlength (x_digits))) ” &&
  “ (m_pre = (Zlength (y_digits))) ”
  &&  (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux

noncomputable def solver_partial_solve_wit_2_pure : Prop :=
  (
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (PreH1 : (retval = (numeral (bx_pre) (x_digits)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 10)) (PreH6 : (2 <= bx_pre)) (PreH7 : (bx_pre <= 40)) (PreH8 : (2 <= basey_pre)) (PreH9 : (basey_pre <= 40)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH11 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH12 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH13 : (n_pre = (Zlength (x_digits)))) (PreH14 : (m_pre = (Zlength (y_digits)))) ,
  ((( &( "vy" ) )) # Int64 |->_)
  ** (intArray.full x_pre n_pre x_digits)
  ** ((( &( "vx" ) )) # Int64 |-> (retval))
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 10) ” &&
  “ (2 <= basey_pre) ” &&
  “ (basey_pre <= 40) ” &&
  “ (m_pre = (Zlength (y_digits))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < m_pre)) -> (((0 : Int) <= (Znth k y_digits (0 : Int))) ∧ ((Znth k y_digits (0 : Int)) < basey_pre))) ”
) \/
(
forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (PreH1 : (retval <= 9223372036854775807)) (PreH2 : (retval >= (-9223372036854775808))) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (basey_pre <= INT_MAX)) (PreH6 : (bx_pre <= INT_MAX)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (basey_pre >= INT_MIN)) (PreH10 : (bx_pre >= INT_MIN)) (PreH11 : (retval = (numeral (bx_pre) (x_digits)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 10)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10)) (PreH16 : (2 <= bx_pre)) (PreH17 : (bx_pre <= 40)) (PreH18 : (2 <= basey_pre)) (PreH19 : (basey_pre <= 40)) (PreH20 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH21 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH22 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH23 : (n_pre = (Zlength (x_digits)))) (PreH24 : (m_pre = (Zlength (y_digits)))) ,
  ((( &( "vy" ) )) # Int64 |->_)
  ** (intArray.full x_pre n_pre x_digits)
  ** ((( &( "vx" ) )) # Int64 |-> (retval))
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < m_pre)) -> (((0 : Int) <= (Znth k y_digits (0 : Int))) ∧ ((Znth k y_digits (0 : Int)) < basey_pre))) ”
)

noncomputable def solver_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (PreH1 : (retval <= 9223372036854775807)) (PreH2 : (retval >= (-9223372036854775808))) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (basey_pre <= INT_MAX)) (PreH6 : (bx_pre <= INT_MAX)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (basey_pre >= INT_MIN)) (PreH10 : (bx_pre >= INT_MIN)) (PreH11 : (retval = (numeral (bx_pre) (x_digits)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 10)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10)) (PreH16 : (2 <= bx_pre)) (PreH17 : (bx_pre <= 40)) (PreH18 : (2 <= basey_pre)) (PreH19 : (basey_pre <= 40)) (PreH20 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH21 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH22 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH23 : (n_pre = (Zlength (x_digits)))) (PreH24 : (m_pre = (Zlength (y_digits)))) ,
  ((( &( "vy" ) )) # Int64 |->_)
  ** (intArray.full x_pre n_pre x_digits)
  ** ((( &( "vx" ) )) # Int64 |-> (retval))
  ** ((( &( "bx" ) )) # Int |-> (bx_pre))
  ** ((( &( "basey" ) )) # Int |-> (basey_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < m_pre)) -> (((0 : Int) <= (Znth k y_digits (0 : Int))) ∧ ((Znth k y_digits (0 : Int)) < basey_pre))) ”

noncomputable def solver_partial_solve_wit_2_aux : Prop :=
  forall (y_digits : (List Int)) (x_digits : (List Int)) (bx_pre : Int) (basey_pre : Int) (x_pre : Int) (n_pre : Int) (y_pre : Int) (m_pre : Int) (retval : Int) (PreH1 : (retval = (numeral (bx_pre) (x_digits)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 10)) (PreH6 : (2 <= bx_pre)) (PreH7 : (bx_pre <= 40)) (PreH8 : (2 <= basey_pre)) (PreH9 : (basey_pre <= 40)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre)))) (PreH11 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre)))) (PreH12 : (Pre bx_pre basey_pre x_digits y_digits)) (PreH13 : (n_pre = (Zlength (x_digits)))) (PreH14 : (m_pre = (Zlength (y_digits)))) ,
  (intArray.full x_pre n_pre x_digits)
  ** (intArray.full y_pre m_pre y_digits)
|--
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 10) ” &&
  “ (2 <= basey_pre) ” &&
  “ (basey_pre <= 40) ” &&
  “ (m_pre = (Zlength (y_digits))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < m_pre)) -> (((0 : Int) <= (Znth k y_digits (0 : Int))) ∧ ((Znth k y_digits (0 : Int)) < basey_pre))) ” &&
  “ (retval = (numeral (bx_pre) (x_digits))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 10) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 10) ” &&
  “ (2 <= bx_pre) ” &&
  “ (bx_pre <= 40) ” &&
  “ (2 <= basey_pre) ” &&
  “ (basey_pre <= 40) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i x_digits (0 : Int))) ∧ ((Znth i x_digits (0 : Int)) < bx_pre))) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> (((0 : Int) <= (Znth i_2 y_digits (0 : Int))) ∧ ((Znth i_2 y_digits (0 : Int)) < basey_pre))) ” &&
  “ (Pre bx_pre basey_pre x_digits y_digits) ” &&
  “ (n_pre = (Zlength (x_digits))) ” &&
  “ (m_pre = (Zlength (y_digits))) ”
  &&  (intArray.full y_pre m_pre y_digits)
  ** (intArray.full x_pre n_pre x_digits)

noncomputable def solver_partial_solve_wit_2 : Prop := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_numeral_value_safety_wit_1 : numeral_value_safety_wit_1
  proof_of_numeral_value_safety_wit_2 : numeral_value_safety_wit_2
  proof_of_numeral_value_safety_wit_3 : numeral_value_safety_wit_3
  proof_of_numeral_value_partial_solve_wit_1 : numeral_value_partial_solve_wit_1
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_numeral_value_safety_wit_4 : numeral_value_safety_wit_4
  proof_of_numeral_value_safety_wit_5 : numeral_value_safety_wit_5
  proof_of_numeral_value_entail_wit_1 : numeral_value_entail_wit_1
  proof_of_numeral_value_entail_wit_2 : numeral_value_entail_wit_2
  proof_of_numeral_value_return_wit_1 : numeral_value_return_wit_1
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure
  proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_goal
