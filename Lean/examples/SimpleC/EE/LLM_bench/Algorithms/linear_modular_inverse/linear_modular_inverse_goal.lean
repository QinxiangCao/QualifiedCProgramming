import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance linear_modular_inverse_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def linear_modular_inverse_safety_wit_1 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** (intArray.undef_seg inverse_pre 1 p_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def linear_modular_inverse_safety_wit_2 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** (intArray.undef_seg inverse_pre 1 p_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def linear_modular_inverse_safety_wit_3 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (((inverse_pre + (1 * sizeof(INT)))) # Int |-> (1))
  ** (intArray.undef_seg inverse_pre (1 + 1) p_pre)
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def linear_modular_inverse_safety_wit_4 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values)) ,
  ((( &( "quotient" ) )) # Int |->_)
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg inverse_pre 1 i values)
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  “ ((p_pre ≠ (INT_MIN)) ∨ (i ≠ (-1))) ” &&
  “ (i ≠ (0 : Int)) ”

noncomputable def linear_modular_inverse_safety_wit_5 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values)) ,
  ((( &( "remainder" ) )) # Int |->_)
  ** ((( &( "quotient" ) )) # Int |-> ((Z.quot p_pre i)))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg inverse_pre 1 i values)
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  “ ((p_pre ≠ (INT_MIN)) ∨ (i ≠ (-1))) ” &&
  “ (i ≠ (0 : Int)) ”

noncomputable def linear_modular_inverse_safety_wit_6 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values)) ,
  (intArray.seg inverse_pre 1 i values)
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "quotient" ) )) # Int |-> (quotient))
  ** ((( &( "remainder" ) )) # Int |-> (remainder))
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  “ ((((p_pre - quotient) * (Znth (remainder - 1) values (0 : Int))) ≠ (INT_MIN)) ∨ (p_pre ≠ (-1))) ” &&
  “ (p_pre ≠ (0 : Int)) ”

noncomputable def linear_modular_inverse_safety_wit_7 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values)) ,
  (intArray.seg inverse_pre 1 i values)
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "quotient" ) )) # Int |-> (quotient))
  ** ((( &( "remainder" ) )) # Int |-> (remainder))
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  “ (((p_pre - quotient) * (Znth (remainder - 1) values (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((p_pre - quotient) * (Znth (remainder - 1) values (0 : Int)))) ”

noncomputable def linear_modular_inverse_safety_wit_8 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "quotient" ) )) # Int |-> (quotient))
  ** ((( &( "remainder" ) )) # Int |-> (remainder))
  ** (intArray.seg inverse_pre 1 i values)
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  “ ((p_pre - quotient) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p_pre - quotient)) ”

noncomputable def linear_modular_inverse_safety_wit_9 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values)) ,
  (intArray.seg inverse_pre 1 (i + 1) (values ++ ((Z.rem ((p_pre - quotient) * (Znth (remainder - 1) values (0 : Int))) p_pre) :: (@List.nil Int))))
  ** (intArray.undef_seg inverse_pre (i + 1) p_pre)
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "inverse" ) )) # Ptr |-> (inverse_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def linear_modular_inverse_entail_wit_1 : Prop :=
  (
forall (inverse_pre : Int) (p_pre : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  (((inverse_pre + (1 * sizeof(INT)))) # Int |-> (1))
  ** (intArray.undef_seg inverse_pre (1 + 1) p_pre)
|--
  EX values : (List Int),
  “ (PrimeForLinearInverse p_pre) ” &&
  “ (2 <= p_pre) ” &&
  “ (p_pre <= 46340) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= p_pre) ” &&
  “ ((Zlength (values)) = (2 - 1)) ” &&
  “ (ModularInversePrefix p_pre 2 values) ”
  &&  (intArray.seg inverse_pre 1 2 values)
  ** (intArray.undef_seg inverse_pre 2 p_pre)
) \/
(
forall (inverse_pre : Int) (p_pre : Int) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (PrimeForLinearInverse p_pre)) (PreH4 : (2 <= p_pre)) (PreH5 : (p_pre <= 46340)) ,
  (((inverse_pre + (1 * sizeof(INT)))) # Int |-> (1))
|--
  EX values : (List Int),
  “ (PrimeForLinearInverse p_pre) ” &&
  “ (2 <= p_pre) ” &&
  “ (p_pre <= 46340) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= p_pre) ” &&
  “ ((Zlength (values)) = (2 - 1)) ” &&
  “ (ModularInversePrefix p_pre 2 values) ”
  &&  (intArray.seg inverse_pre 1 2 values)
)

noncomputable def linear_modular_inverse_entail_wit_2 : Prop :=
  (
forall (inverse_pre : Int) (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  (intArray.seg inverse_pre 1 i values_2)
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  EX values : (List Int),
  “ (PrimeForLinearInverse p_pre) ” &&
  “ (2 <= p_pre) ” &&
  “ (p_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i < p_pre) ” &&
  “ ((Z.quot p_pre i) = (Z.quot p_pre i)) ” &&
  “ ((Z.rem p_pre i) = (Z.rem p_pre i)) ” &&
  “ (1 <= (Z.rem p_pre i)) ” &&
  “ ((Z.rem p_pre i) < i) ” &&
  “ ((0 : Int) < (p_pre - (Z.quot p_pre i))) ” &&
  “ ((p_pre - (Z.quot p_pre i)) < p_pre) ” &&
  “ ((0 : Int) < (Znth ((Z.rem p_pre i) - 1) values (0 : Int))) ” &&
  “ ((Znth ((Z.rem p_pre i) - 1) values (0 : Int)) < p_pre) ” &&
  “ ((Zlength (values)) = (i - 1)) ” &&
  “ (ModularInversePrefix p_pre i values) ”
  &&  (intArray.seg inverse_pre 1 i values)
  ** (intArray.undef_seg inverse_pre i p_pre)
) \/
(
forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  TT && emp 
|--
  “ ((Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int)) < p_pre) ” &&
  “ ((0 : Int) < (Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int))) ” &&
  “ ((p_pre - (Z.quot p_pre i)) < p_pre) ” &&
  “ ((0 : Int) < (p_pre - (Z.quot p_pre i))) ” &&
  “ ((Z.rem p_pre i) < i) ” &&
  “ (1 <= (Z.rem p_pre i)) ”
  &&  emp
)

noncomputable def linear_modular_inverse_entail_wit_2_split_goal_1 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  ((Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int)) < p_pre)

noncomputable def linear_modular_inverse_entail_wit_2_split_goal_2 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  ((0 : Int) < (Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int)))

noncomputable def linear_modular_inverse_entail_wit_2_split_goal_3 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  ((p_pre - (Z.quot p_pre i)) < p_pre)

noncomputable def linear_modular_inverse_entail_wit_2_split_goal_4 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  ((0 : Int) < (p_pre - (Z.quot p_pre i)))

noncomputable def linear_modular_inverse_entail_wit_2_split_goal_5 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  ((Z.rem p_pre i) < i)

noncomputable def linear_modular_inverse_entail_wit_2_split_goal_6 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  (1 <= (Z.rem p_pre i))

noncomputable def linear_modular_inverse_entail_wit_3 : Prop :=
  (
forall (inverse_pre : Int) (p_pre : Int) (values_2 : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values_2 (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values_2 (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values_2)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values_2)) ,
  (intArray.seg inverse_pre 1 (i + 1) (values_2 ++ ((Z.rem ((p_pre - quotient) * (Znth (remainder - 1) values_2 (0 : Int))) p_pre) :: (@List.nil Int))))
  ** (intArray.undef_seg inverse_pre (i + 1) p_pre)
|--
  EX values : (List Int),
  “ (PrimeForLinearInverse p_pre) ” &&
  “ (2 <= p_pre) ” &&
  “ (p_pre <= 46340) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= p_pre) ” &&
  “ ((Zlength (values)) = ((i + 1) - 1)) ” &&
  “ (ModularInversePrefix p_pre (i + 1) values) ”
  &&  (intArray.seg inverse_pre 1 (i + 1) values)
  ** (intArray.undef_seg inverse_pre (i + 1) p_pre)
) \/
(
forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values_2 (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values_2 (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values_2)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values_2)) ,
  TT && emp 
|--
  “ (ModularInversePrefix p_pre (i + 1) (values_2 ++ ((Z.rem ((p_pre - (Z.quot p_pre i)) * (Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int))) p_pre) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((values_2 ++ ((Z.rem ((p_pre - (Z.quot p_pre i)) * (Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int))) p_pre) :: (@List.nil Int))))) = ((i + 1) - 1)) ”
  &&  emp
)

noncomputable def linear_modular_inverse_entail_wit_3_split_goal_1 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values_2 (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values_2 (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values_2)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values_2)) ,
  (ModularInversePrefix p_pre (i + 1) (values_2 ++ ((Z.rem ((p_pre - (Z.quot p_pre i)) * (Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int))) p_pre) :: (@List.nil Int))))

noncomputable def linear_modular_inverse_entail_wit_3_split_goal_2 : Prop :=
  forall (p_pre : Int) (values_2 : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values_2 (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values_2 (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values_2)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values_2)) ,
  ((Zlength ((values_2 ++ ((Z.rem ((p_pre - (Z.quot p_pre i)) * (Znth ((Z.rem p_pre i) - 1) values_2 (0 : Int))) p_pre) :: (@List.nil Int))))) = ((i + 1) - 1))

noncomputable def linear_modular_inverse_return_wit_1 : Prop :=
  (
forall (inverse_pre : Int) (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i >= p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  (intArray.seg inverse_pre 1 i values_2)
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  EX values : (List Int),
  “ (ModularInversePrefix p_pre p_pre values) ”
  &&  (intArray.seg inverse_pre 1 p_pre values)
) \/
(
forall (inverse_pre : Int) (p_pre : Int) (values_2 : (List Int)) (i : Int) (PreH1 : (i >= p_pre)) (PreH2 : (PrimeForLinearInverse p_pre)) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : ((Zlength (values_2)) = (i - 1))) (PreH8 : (ModularInversePrefix p_pre i values_2)) ,
  (intArray.seg inverse_pre 1 i values_2)
|--
  EX values : (List Int),
  “ (ModularInversePrefix p_pre p_pre values) ”
  &&  (intArray.seg inverse_pre 1 p_pre values)
)

noncomputable def linear_modular_inverse_partial_solve_wit_1 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  (intArray.undef_seg inverse_pre 1 p_pre)
|--
  “ (PrimeForLinearInverse p_pre) ” &&
  “ (2 <= p_pre) ” &&
  “ (p_pre <= 46340) ”
  &&  (((inverse_pre + (1 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg inverse_pre (1 + 1) p_pre)

noncomputable def linear_modular_inverse_partial_solve_wit_2 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values)) ,
  (intArray.seg inverse_pre 1 i values)
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  “ (PrimeForLinearInverse p_pre) ” &&
  “ (2 <= p_pre) ” &&
  “ (p_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i < p_pre) ” &&
  “ (quotient = (Z.quot p_pre i)) ” &&
  “ (remainder = (Z.rem p_pre i)) ” &&
  “ (1 <= remainder) ” &&
  “ (remainder < i) ” &&
  “ ((0 : Int) < (p_pre - quotient)) ” &&
  “ ((p_pre - quotient) < p_pre) ” &&
  “ ((0 : Int) < (Znth (remainder - 1) values (0 : Int))) ” &&
  “ ((Znth (remainder - 1) values (0 : Int)) < p_pre) ” &&
  “ ((Zlength (values)) = (i - 1)) ” &&
  “ (ModularInversePrefix p_pre i values) ”
  &&  (((inverse_pre + (remainder * sizeof(INT)))) # Int |-> ((Znth (remainder - 1) values (0 : Int))))
  ** (intArray.missing_i inverse_pre remainder 1 i values)
  ** (intArray.undef_seg inverse_pre i p_pre)

noncomputable def linear_modular_inverse_partial_solve_wit_3 : Prop :=
  forall (inverse_pre : Int) (p_pre : Int) (values : (List Int)) (i : Int) (quotient : Int) (remainder : Int) (PreH1 : (PrimeForLinearInverse p_pre)) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (Z.quot p_pre i))) (PreH7 : (remainder = (Z.rem p_pre i))) (PreH8 : (1 <= remainder)) (PreH9 : (remainder < i)) (PreH10 : ((0 : Int) < (p_pre - quotient))) (PreH11 : ((p_pre - quotient) < p_pre)) (PreH12 : ((0 : Int) < (Znth (remainder - 1) values (0 : Int)))) (PreH13 : ((Znth (remainder - 1) values (0 : Int)) < p_pre)) (PreH14 : ((Zlength (values)) = (i - 1))) (PreH15 : (ModularInversePrefix p_pre i values)) ,
  (intArray.seg inverse_pre 1 i values)
  ** (intArray.undef_seg inverse_pre i p_pre)
|--
  “ (PrimeForLinearInverse p_pre) ” &&
  “ (2 <= p_pre) ” &&
  “ (p_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i < p_pre) ” &&
  “ (quotient = (Z.quot p_pre i)) ” &&
  “ (remainder = (Z.rem p_pre i)) ” &&
  “ (1 <= remainder) ” &&
  “ (remainder < i) ” &&
  “ ((0 : Int) < (p_pre - quotient)) ” &&
  “ ((p_pre - quotient) < p_pre) ” &&
  “ ((0 : Int) < (Znth (remainder - 1) values (0 : Int))) ” &&
  “ ((Znth (remainder - 1) values (0 : Int)) < p_pre) ” &&
  “ ((Zlength (values)) = (i - 1)) ” &&
  “ (ModularInversePrefix p_pre i values) ”
  &&  (((inverse_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg inverse_pre (i + 1) p_pre)
  ** (intArray.seg inverse_pre 1 i values)


structure VC_Correct : Type where
  proof_of_linear_modular_inverse_safety_wit_1 : linear_modular_inverse_safety_wit_1
  proof_of_linear_modular_inverse_safety_wit_2 : linear_modular_inverse_safety_wit_2
  proof_of_linear_modular_inverse_safety_wit_3 : linear_modular_inverse_safety_wit_3
  proof_of_linear_modular_inverse_safety_wit_4 : linear_modular_inverse_safety_wit_4
  proof_of_linear_modular_inverse_safety_wit_5 : linear_modular_inverse_safety_wit_5
  proof_of_linear_modular_inverse_safety_wit_6 : linear_modular_inverse_safety_wit_6
  proof_of_linear_modular_inverse_safety_wit_7 : linear_modular_inverse_safety_wit_7
  proof_of_linear_modular_inverse_safety_wit_8 : linear_modular_inverse_safety_wit_8
  proof_of_linear_modular_inverse_safety_wit_9 : linear_modular_inverse_safety_wit_9
  proof_of_linear_modular_inverse_partial_solve_wit_1 : linear_modular_inverse_partial_solve_wit_1
  proof_of_linear_modular_inverse_partial_solve_wit_2 : linear_modular_inverse_partial_solve_wit_2
  proof_of_linear_modular_inverse_partial_solve_wit_3 : linear_modular_inverse_partial_solve_wit_3
  proof_of_linear_modular_inverse_entail_wit_1 : linear_modular_inverse_entail_wit_1
  proof_of_linear_modular_inverse_entail_wit_2 : linear_modular_inverse_entail_wit_2
  proof_of_linear_modular_inverse_entail_wit_3 : linear_modular_inverse_entail_wit_3
  proof_of_linear_modular_inverse_return_wit_1 : linear_modular_inverse_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_goal
