import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance modular_inverse_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def modular_inverse_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH2 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (1 < modulus_pre)) (PreH4 : ((0 : Int) < a_pre)) (PreH5 : (a_pre < modulus_pre)) (PreH6 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ ((x_callee_v ≠ (INT_MIN)) ∨ (modulus_pre ≠ (-1))) ” &&
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def modular_inverse_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH2 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (1 < modulus_pre)) (PreH4 : ((0 : Int) < a_pre)) (PreH5 : (a_pre < modulus_pre)) (PreH6 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int |-> ((Z.rem x_callee_v modulus_pre)))
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def modular_inverse_safety_wit_3 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int |-> ((Z.rem x_callee_v modulus_pre)))
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (((Z.rem x_callee_v modulus_pre) + modulus_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ”

noncomputable def modular_inverse_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ ((0 : Int) <= ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ” &&
  “ (((Z.rem x_callee_v modulus_pre) + modulus_pre) < modulus_pre) ” &&
  “ (ModularInverse a_pre modulus_pre ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (ModularInverse a_pre modulus_pre ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ” &&
  “ ((0 : Int) <= ((Z.rem x_callee_v modulus_pre) + modulus_pre)) ”
  &&  emp
)

noncomputable def modular_inverse_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  (ModularInverse a_pre modulus_pre ((Z.rem x_callee_v modulus_pre) + modulus_pre))

noncomputable def modular_inverse_return_wit_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) < (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((0 : Int) <= ((Z.rem x_callee_v modulus_pre) + modulus_pre))

noncomputable def modular_inverse_return_wit_2 : Prop :=
  (
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) >= (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ ((0 : Int) <= (Z.rem x_callee_v modulus_pre)) ” &&
  “ ((Z.rem x_callee_v modulus_pre) < modulus_pre) ” &&
  “ (ModularInverse a_pre modulus_pre (Z.rem x_callee_v modulus_pre)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) >= (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (ModularInverse a_pre modulus_pre (Z.rem x_callee_v modulus_pre)) ” &&
  “ ((Z.rem x_callee_v modulus_pre) < modulus_pre) ”
  &&  emp
)

noncomputable def modular_inverse_return_wit_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) >= (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  (ModularInverse a_pre modulus_pre (Z.rem x_callee_v modulus_pre))

noncomputable def modular_inverse_return_wit_2_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((Z.rem x_callee_v modulus_pre) >= (0 : Int))) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v) + (modulus_pre * y_callee_v)) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : ((0 : Int) < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((Z.rem x_callee_v modulus_pre) < modulus_pre)

noncomputable def modular_inverse_partial_solve_wit_1_pure : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (PreH1 : (1 < modulus_pre)) (PreH2 : ((0 : Int) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "g" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "modulus" ) )) # Int |-> (modulus_pre))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (INT_MIN < modulus_pre) ” &&
  “ (modulus_pre <= INT_MAX) ” &&
  “ (a_pre <= INT_MAX) ”

noncomputable def modular_inverse_partial_solve_wit_1_aux : Prop :=
  forall (modulus_pre : Int) (a_pre : Int) (PreH1 : (1 < modulus_pre)) (PreH2 : ((0 : Int) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (INT_MIN < a_pre) ” &&
  “ (INT_MIN < modulus_pre) ” &&
  “ (modulus_pre <= INT_MAX) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (1 < modulus_pre) ” &&
  “ ((0 : Int) < a_pre) ” &&
  “ (a_pre < modulus_pre) ” &&
  “ ((Zgcd (a_pre) (modulus_pre)) = 1) ”
  &&  emp

noncomputable def modular_inverse_partial_solve_wit_1 : Prop := modular_inverse_partial_solve_wit_1_pure -> modular_inverse_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_modular_inverse_safety_wit_1 : modular_inverse_safety_wit_1
  proof_of_modular_inverse_safety_wit_2 : modular_inverse_safety_wit_2
  proof_of_modular_inverse_safety_wit_3 : modular_inverse_safety_wit_3
  proof_of_modular_inverse_partial_solve_wit_1_pure : modular_inverse_partial_solve_wit_1_pure
  proof_of_modular_inverse_partial_solve_wit_1 : modular_inverse_partial_solve_wit_1
  proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1
  proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2

end SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_goal
