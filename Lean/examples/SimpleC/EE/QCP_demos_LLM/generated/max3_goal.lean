import SimpleC.SL.SeparationLogic


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.max3_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance max3_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def max3_return_wit_1 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre >= z_pre)) (PreH2 : (x_pre >= y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre >= x_pre) ” &&
  “ (x_pre >= y_pre) ” &&
  “ (x_pre >= z_pre) ”
  &&  emp

noncomputable def max3_return_wit_2 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre < z_pre)) (PreH2 : (x_pre >= y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (z_pre >= x_pre) ” &&
  “ (z_pre >= y_pre) ” &&
  “ (z_pre >= z_pre) ”
  &&  emp

noncomputable def max3_return_wit_3 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (y_pre >= z_pre)) (PreH2 : (x_pre < y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (y_pre >= x_pre) ” &&
  “ (y_pre >= y_pre) ” &&
  “ (y_pre >= z_pre) ”
  &&  emp

noncomputable def max3_return_wit_4 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (y_pre < z_pre)) (PreH2 : (x_pre < y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (z_pre >= x_pre) ” &&
  “ (z_pre >= y_pre) ” &&
  “ (z_pre >= z_pre) ”
  &&  emp


structure VC_Correct : Type where
  proof_of_max3_return_wit_1 : max3_return_wit_1
  proof_of_max3_return_wit_2 : max3_return_wit_2
  proof_of_max3_return_wit_3 : max3_return_wit_3
  proof_of_max3_return_wit_4 : max3_return_wit_4

end SimpleC.EE.QCP_demos_LLM.generated.max3_goal
