import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance modular_power_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def modular_power_safety_wit_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_power_safety_wit_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (2 <= modulus_pre)) (PreH2 : (modulus_pre <= 100000)) (PreH3 : ((0 : Int) <= a)) (PreH4 : (a < modulus_pre)) (PreH5 : ((0 : Int) <= b)) (PreH6 : ((0 : Int) <= result)) (PreH7 : (result < modulus_pre)) (PreH8 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_power_safety_wit_3 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b > (0 : Int))) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : ((0 : Int) <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : ((0 : Int) <= b)) (PreH7 : ((0 : Int) <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_4 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b > (0 : Int))) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : ((0 : Int) <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : ((0 : Int) <= b)) (PreH7 : ((0 : Int) <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_safety_wit_5 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b > (0 : Int))) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : ((0 : Int) <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : ((0 : Int) <= b)) (PreH7 : ((0 : Int) <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_power_safety_wit_6 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((result * a) ≠ (-9223372036854775808)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_7 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result * a) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (result * a)) ”

noncomputable def modular_power_safety_wit_8 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))))
|--
  “ (((a * a) ≠ (-9223372036854775808)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_9 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))))
|--
  “ ((a * a) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (a * a)) ”

noncomputable def modular_power_safety_wit_10 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((a * a) ≠ (-9223372036854775808)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_11 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((a * a) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (a * a)) ”

noncomputable def modular_power_safety_wit_12 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_13 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> ((signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_safety_wit_14 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_power_safety_wit_15 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "a" ) )) # Int |-> ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_power_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < modulus_pre) ” &&
  “ (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_1_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (PreH1 : ((0 : Int) <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : ((0 : Int) <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1)

noncomputable def modular_power_entail_wit_2_1 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32)) < modulus_pre) ” &&
  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) (Z.quot b 2) (signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) (Z.quot b 2) (signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32)) < modulus_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32))) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) < modulus_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_2_1_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) (Z.quot b 2) (signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32)))

noncomputable def modular_power_entail_wit_2_1_split_goal_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32)) < modulus_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_3 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem (result * a) modulus_pre)) (32)))

noncomputable def modular_power_entail_wit_2_1_split_goal_4 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_power_entail_wit_2_1_split_goal_5 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) < modulus_pre)

noncomputable def modular_power_entail_wit_2_1_split_goal_6 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)))

noncomputable def modular_power_entail_wit_2_2 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < modulus_pre) ” &&
  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) (Z.quot b 2) result) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) (Z.quot b 2) result) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) < modulus_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32))) ”
  &&  emp
)

noncomputable def modular_power_entail_wit_2_2_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) (Z.quot b 2) result)

noncomputable def modular_power_entail_wit_2_2_split_goal_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_power_entail_wit_2_2_split_goal_3 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)) < modulus_pre)

noncomputable def modular_power_entail_wit_2_2_split_goal_4 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : ((0 : Int) <= b)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem (a * a) modulus_pre)) (32)))

noncomputable def modular_power_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : ((0 : Int) <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : ((0 : Int) <= b)) (PreH7 : ((0 : Int) <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (ModularPower a_pre b_pre modulus_pre result) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : ((0 : Int) <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : ((0 : Int) <= b)) (PreH7 : ((0 : Int) <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  TT && emp 
|--
  “ (ModularPower a_pre b_pre modulus_pre result) ”
  &&  emp
)

noncomputable def modular_power_return_wit_1_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (modulus_pre : Int) (result : Int) (b : Int) (a : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : ((0 : Int) <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : ((0 : Int) <= b)) (PreH7 : ((0 : Int) <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result)) ,
  (ModularPower a_pre b_pre modulus_pre result)


structure VC_Correct : Type where
  proof_of_modular_power_safety_wit_1 : modular_power_safety_wit_1
  proof_of_modular_power_safety_wit_2 : modular_power_safety_wit_2
  proof_of_modular_power_safety_wit_3 : modular_power_safety_wit_3
  proof_of_modular_power_safety_wit_4 : modular_power_safety_wit_4
  proof_of_modular_power_safety_wit_5 : modular_power_safety_wit_5
  proof_of_modular_power_safety_wit_6 : modular_power_safety_wit_6
  proof_of_modular_power_safety_wit_7 : modular_power_safety_wit_7
  proof_of_modular_power_safety_wit_8 : modular_power_safety_wit_8
  proof_of_modular_power_safety_wit_9 : modular_power_safety_wit_9
  proof_of_modular_power_safety_wit_10 : modular_power_safety_wit_10
  proof_of_modular_power_safety_wit_11 : modular_power_safety_wit_11
  proof_of_modular_power_safety_wit_12 : modular_power_safety_wit_12
  proof_of_modular_power_safety_wit_13 : modular_power_safety_wit_13
  proof_of_modular_power_safety_wit_14 : modular_power_safety_wit_14
  proof_of_modular_power_safety_wit_15 : modular_power_safety_wit_15
  proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1
  proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1
  proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2
  proof_of_modular_power_return_wit_1 : modular_power_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_goal
