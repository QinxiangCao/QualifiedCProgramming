import SimpleC.SL.SeparationLogic


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.abs_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance abs_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def abs_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def abs_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ (x_pre ≠ (INT_MIN)) ”

noncomputable def abs_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
)

noncomputable def abs_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (x_pre = (Zabs (x_pre)))

noncomputable def abs_return_wit_2 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
)

noncomputable def abs_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((-x_pre) = (Zabs (x_pre)))


structure VC_Correct : Type where
  proof_of_abs_safety_wit_1 : abs_safety_wit_1
  proof_of_abs_safety_wit_2 : abs_safety_wit_2
  proof_of_abs_return_wit_1 : abs_return_wit_1
  proof_of_abs_return_wit_2 : abs_return_wit_2

end SimpleC.EE.QCP_demos_LLM.generated.abs_goal
