import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance modular_mul_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def modular_mul_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (((0 : Int) - modulus_pre) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : ((0 : Int) < modulus_pre)) (PreH6 : ((modulus_pre * 2) <= INT_MAX)) ,
  ((( &( "res" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_mul_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (((0 : Int) - modulus_pre) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : ((0 : Int) < modulus_pre)) (PreH6 : ((modulus_pre * 2) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int |->_)
  ** ((( &( "res" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_mul_safety_wit_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (((0 : Int) - modulus_pre) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : ((0 : Int) < modulus_pre)) (PreH6 : ((modulus_pre * 2) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int |-> (1))
  ** ((( &( "res" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_mul_safety_wit_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre < (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int |-> (1))
  ** ((( &( "res" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (b_pre ≠ (INT_MIN)) ”

noncomputable def modular_mul_safety_wit_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre < (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int |-> (1))
  ** ((( &( "res" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> ((-b_pre)))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def modular_mul_safety_wit_6 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre < (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int |-> (1))
  ** ((( &( "res" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> ((-b_pre)))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_mul_safety_wit_7 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((0 : Int) < modulus_pre)) (PreH2 : ((modulus_pre * 2) <= INT_MAX)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= INT_MAX)) (PreH5 : (flag = ((0 : Int) - 1))) (PreH6 : (((0 : Int) - modulus_pre) < a)) (PreH7 : (a < modulus_pre)) (PreH8 : (((0 : Int) - modulus_pre) < res)) (PreH9 : (res < modulus_pre)) (PreH10 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_mul_safety_wit_8 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((0 : Int) < modulus_pre)) (PreH2 : ((modulus_pre * 2) <= INT_MAX)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= INT_MAX)) (PreH5 : (flag = 1)) (PreH6 : (((0 : Int) - modulus_pre) < a)) (PreH7 : (a < modulus_pre)) (PreH8 : (((0 : Int) - modulus_pre) < res)) (PreH9 : (res < modulus_pre)) (PreH10 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_mul_safety_wit_9 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = 1)) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_10 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = ((0 : Int) - 1))) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_11 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = ((0 : Int) - 1))) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_mul_safety_wit_12 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = 1)) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_mul_safety_wit_13 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = ((0 : Int) - 1))) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_mul_safety_wit_14 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b > (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = 1)) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def modular_mul_safety_wit_15 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (((res + a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_16 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((res + a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (res + a)) ”

noncomputable def modular_mul_safety_wit_17 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (((res + a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_18 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((res + a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (res + a)) ”

noncomputable def modular_mul_safety_wit_19 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_20 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_mul_safety_wit_21 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_22 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_mul_safety_wit_23 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_24 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_mul_safety_wit_25 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((b ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_26 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def modular_mul_safety_wit_27 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ (((a + a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_28 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ ((a + a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a + a)) ”

noncomputable def modular_mul_safety_wit_29 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ (((a + a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_30 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> ((Z.rem (res + a) modulus_pre)))
|--
  “ ((a + a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a + a)) ”

noncomputable def modular_mul_safety_wit_31 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (((a + a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_32 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((a + a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a + a)) ”

noncomputable def modular_mul_safety_wit_33 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ (((a + a) ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_mul_safety_wit_34 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> ((Z.quot b 2)))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((a + a) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a + a)) ”

noncomputable def modular_mul_safety_wit_35 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = 1)) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((res * flag) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (res * flag)) ”

noncomputable def modular_mul_safety_wit_36 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = ((0 : Int) - 1))) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((( &( "modulus" ) )) # Int |-> (modulus_pre))
  ** ((( &( "b" ) )) # Int |-> (b))
  ** ((( &( "flag" ) )) # Int |-> (flag))
  ** ((( &( "a" ) )) # Int |-> (a))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((res * flag) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (res * flag)) ”

noncomputable def modular_mul_entail_wit_1_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre < (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) < modulus_pre) ” &&
  “ ((modulus_pre * 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (-b_pre)) ” &&
  “ ((-b_pre) <= INT_MAX) ” &&
  “ ((-1) = ((0 : Int) - 1)) ” &&
  “ (((0 : Int) - modulus_pre) < a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (0 : Int)) ” &&
  “ ((0 : Int) < modulus_pre) ” &&
  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre (-b_pre) (0 : Int) (-1)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre < (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre (-b_pre) (0 : Int) (-1)) ”
  &&  emp
)

noncomputable def modular_mul_entail_wit_1_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre < (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  (ModularMulProgress a_pre b_pre modulus_pre a_pre (-b_pre) (0 : Int) (-1))

noncomputable def modular_mul_entail_wit_1_2 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre >= (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) < modulus_pre) ” &&
  “ ((modulus_pre * 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ (b_pre <= INT_MAX) ” &&
  “ (1 = 1) ” &&
  “ (((0 : Int) - modulus_pre) < a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (0 : Int)) ” &&
  “ ((0 : Int) < modulus_pre) ” &&
  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre b_pre (0 : Int) 1) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre >= (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre b_pre (0 : Int) 1) ”
  &&  emp
)

noncomputable def modular_mul_entail_wit_1_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre >= (0 : Int))) (PreH2 : (((0 : Int) - modulus_pre) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : ((0 : Int) < modulus_pre)) (PreH7 : ((modulus_pre * 2) <= INT_MAX)) ,
  (ModularMulProgress a_pre b_pre modulus_pre a_pre b_pre (0 : Int) 1)

noncomputable def modular_mul_entail_wit_2_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ ((0 : Int) < modulus_pre) ” &&
  “ ((modulus_pre * 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ (flag = ((0 : Int) - 1)) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (res + a) modulus_pre)) ” &&
  “ ((Z.rem (res + a) modulus_pre) < modulus_pre) ” &&
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) (Z.rem (res + a) modulus_pre) flag) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) (Z.rem (res + a) modulus_pre) ((0 : Int) - 1)) ” &&
  “ ((Z.rem (res + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (res + a) modulus_pre)) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ”
  &&  emp
)

noncomputable def modular_mul_entail_wit_2_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) (Z.rem (res + a) modulus_pre) ((0 : Int) - 1))

noncomputable def modular_mul_entail_wit_2_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.rem (res + a) modulus_pre) < modulus_pre)

noncomputable def modular_mul_entail_wit_2_1_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (((0 : Int) - modulus_pre) < (Z.rem (res + a) modulus_pre))

noncomputable def modular_mul_entail_wit_2_1_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.rem (a + a) modulus_pre) < modulus_pre)

noncomputable def modular_mul_entail_wit_2_1_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre))

noncomputable def modular_mul_entail_wit_2_1_split_goal_6 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.quot b 2) <= INT_MAX)

noncomputable def modular_mul_entail_wit_2_1_split_goal_7 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_mul_entail_wit_2_2 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ ((0 : Int) < modulus_pre) ” &&
  “ ((modulus_pre * 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ (flag = 1) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (res + a) modulus_pre)) ” &&
  “ ((Z.rem (res + a) modulus_pre) < modulus_pre) ” &&
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) (Z.rem (res + a) modulus_pre) flag) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) (Z.rem (res + a) modulus_pre) 1) ” &&
  “ ((Z.rem (res + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (res + a) modulus_pre)) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ”
  &&  emp
)

noncomputable def modular_mul_entail_wit_2_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) (Z.rem (res + a) modulus_pre) 1)

noncomputable def modular_mul_entail_wit_2_2_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.rem (res + a) modulus_pre) < modulus_pre)

noncomputable def modular_mul_entail_wit_2_2_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (((0 : Int) - modulus_pre) < (Z.rem (res + a) modulus_pre))

noncomputable def modular_mul_entail_wit_2_2_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.rem (a + a) modulus_pre) < modulus_pre)

noncomputable def modular_mul_entail_wit_2_2_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre))

noncomputable def modular_mul_entail_wit_2_2_split_goal_6 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.quot b 2) <= INT_MAX)

noncomputable def modular_mul_entail_wit_2_2_split_goal_7 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) = 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_mul_entail_wit_2_3 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ ((0 : Int) < modulus_pre) ” &&
  “ ((modulus_pre * 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ (flag = ((0 : Int) - 1)) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < res) ” &&
  “ (res < modulus_pre) ” &&
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) res flag) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) res ((0 : Int) - 1)) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ”
  &&  emp
)

noncomputable def modular_mul_entail_wit_2_3_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) res ((0 : Int) - 1))

noncomputable def modular_mul_entail_wit_2_3_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.rem (a + a) modulus_pre) < modulus_pre)

noncomputable def modular_mul_entail_wit_2_3_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre))

noncomputable def modular_mul_entail_wit_2_3_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.quot b 2) <= INT_MAX)

noncomputable def modular_mul_entail_wit_2_3_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = ((0 : Int) - 1))) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_mul_entail_wit_2_4 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ ((0 : Int) < modulus_pre) ” &&
  “ ((modulus_pre * 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ (flag = 1) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < res) ” &&
  “ (res < modulus_pre) ” &&
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) res flag) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) res 1) ” &&
  “ ((Z.rem (a + a) modulus_pre) < modulus_pre) ” &&
  “ (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre)) ” &&
  “ ((Z.quot b 2) <= INT_MAX) ” &&
  “ ((0 : Int) <= (Z.quot b 2)) ”
  &&  emp
)

noncomputable def modular_mul_entail_wit_2_4_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a + a) modulus_pre) (Z.quot b 2) res 1)

noncomputable def modular_mul_entail_wit_2_4_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.rem (a + a) modulus_pre) < modulus_pre)

noncomputable def modular_mul_entail_wit_2_4_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (((0 : Int) - modulus_pre) < (Z.rem (a + a) modulus_pre))

noncomputable def modular_mul_entail_wit_2_4_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((Z.quot b 2) <= INT_MAX)

noncomputable def modular_mul_entail_wit_2_4_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : ((Z.rem b 2) ≠ 1)) (PreH2 : (b > (0 : Int))) (PreH3 : ((0 : Int) < modulus_pre)) (PreH4 : ((modulus_pre * 2) <= INT_MAX)) (PreH5 : ((0 : Int) <= b)) (PreH6 : (b <= INT_MAX)) (PreH7 : (flag = 1)) (PreH8 : (((0 : Int) - modulus_pre) < a)) (PreH9 : (a < modulus_pre)) (PreH10 : (((0 : Int) - modulus_pre) < res)) (PreH11 : (res < modulus_pre)) (PreH12 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  ((0 : Int) <= (Z.quot b 2))

noncomputable def modular_mul_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = ((0 : Int) - 1))) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * flag)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = ((0 : Int) - 1))) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * ((0 : Int) - 1))) ”
  &&  emp
)

noncomputable def modular_mul_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = ((0 : Int) - 1))) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (ModularMul a_pre b_pre modulus_pre (res * ((0 : Int) - 1)))

noncomputable def modular_mul_return_wit_2 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = 1)) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * flag)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = 1)) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * 1)) ”
  &&  emp
)

noncomputable def modular_mul_return_wit_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (res : Int) (a : Int) (flag : Int) (b : Int) (PreH1 : (b <= (0 : Int))) (PreH2 : ((0 : Int) < modulus_pre)) (PreH3 : ((modulus_pre * 2) <= INT_MAX)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : (flag = 1)) (PreH7 : (((0 : Int) - modulus_pre) < a)) (PreH8 : (a < modulus_pre)) (PreH9 : (((0 : Int) - modulus_pre) < res)) (PreH10 : (res < modulus_pre)) (PreH11 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag)) ,
  (ModularMul a_pre b_pre modulus_pre (res * 1))


structure VC_Correct : Type where
  proof_of_modular_mul_safety_wit_1 : modular_mul_safety_wit_1
  proof_of_modular_mul_safety_wit_2 : modular_mul_safety_wit_2
  proof_of_modular_mul_safety_wit_3 : modular_mul_safety_wit_3
  proof_of_modular_mul_safety_wit_4 : modular_mul_safety_wit_4
  proof_of_modular_mul_safety_wit_5 : modular_mul_safety_wit_5
  proof_of_modular_mul_safety_wit_6 : modular_mul_safety_wit_6
  proof_of_modular_mul_safety_wit_7 : modular_mul_safety_wit_7
  proof_of_modular_mul_safety_wit_8 : modular_mul_safety_wit_8
  proof_of_modular_mul_safety_wit_9 : modular_mul_safety_wit_9
  proof_of_modular_mul_safety_wit_10 : modular_mul_safety_wit_10
  proof_of_modular_mul_safety_wit_11 : modular_mul_safety_wit_11
  proof_of_modular_mul_safety_wit_12 : modular_mul_safety_wit_12
  proof_of_modular_mul_safety_wit_13 : modular_mul_safety_wit_13
  proof_of_modular_mul_safety_wit_14 : modular_mul_safety_wit_14
  proof_of_modular_mul_safety_wit_15 : modular_mul_safety_wit_15
  proof_of_modular_mul_safety_wit_16 : modular_mul_safety_wit_16
  proof_of_modular_mul_safety_wit_17 : modular_mul_safety_wit_17
  proof_of_modular_mul_safety_wit_18 : modular_mul_safety_wit_18
  proof_of_modular_mul_safety_wit_19 : modular_mul_safety_wit_19
  proof_of_modular_mul_safety_wit_20 : modular_mul_safety_wit_20
  proof_of_modular_mul_safety_wit_21 : modular_mul_safety_wit_21
  proof_of_modular_mul_safety_wit_22 : modular_mul_safety_wit_22
  proof_of_modular_mul_safety_wit_23 : modular_mul_safety_wit_23
  proof_of_modular_mul_safety_wit_24 : modular_mul_safety_wit_24
  proof_of_modular_mul_safety_wit_25 : modular_mul_safety_wit_25
  proof_of_modular_mul_safety_wit_26 : modular_mul_safety_wit_26
  proof_of_modular_mul_safety_wit_27 : modular_mul_safety_wit_27
  proof_of_modular_mul_safety_wit_28 : modular_mul_safety_wit_28
  proof_of_modular_mul_safety_wit_29 : modular_mul_safety_wit_29
  proof_of_modular_mul_safety_wit_30 : modular_mul_safety_wit_30
  proof_of_modular_mul_safety_wit_31 : modular_mul_safety_wit_31
  proof_of_modular_mul_safety_wit_32 : modular_mul_safety_wit_32
  proof_of_modular_mul_safety_wit_33 : modular_mul_safety_wit_33
  proof_of_modular_mul_safety_wit_34 : modular_mul_safety_wit_34
  proof_of_modular_mul_safety_wit_35 : modular_mul_safety_wit_35
  proof_of_modular_mul_safety_wit_36 : modular_mul_safety_wit_36
  proof_of_modular_mul_entail_wit_1_1 : modular_mul_entail_wit_1_1
  proof_of_modular_mul_entail_wit_1_2 : modular_mul_entail_wit_1_2
  proof_of_modular_mul_entail_wit_2_1 : modular_mul_entail_wit_2_1
  proof_of_modular_mul_entail_wit_2_2 : modular_mul_entail_wit_2_2
  proof_of_modular_mul_entail_wit_2_3 : modular_mul_entail_wit_2_3
  proof_of_modular_mul_entail_wit_2_4 : modular_mul_entail_wit_2_4
  proof_of_modular_mul_return_wit_1 : modular_mul_return_wit_1
  proof_of_modular_mul_return_wit_2 : modular_mul_return_wit_2

end SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_goal
