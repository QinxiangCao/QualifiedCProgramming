import SimpleC.SL.LeanPrinterPrelude


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.delta_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance delta_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def delta_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre < y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((y_pre - x_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (y_pre - x_pre)) ”

noncomputable def delta_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre >= y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((x_pre - y_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_pre - y_pre)) ”

noncomputable def delta_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre >= y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((x_pre - y_pre) = (Z.abs ((x_pre - y_pre)))) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre >= y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((x_pre - y_pre) = (Z.abs ((x_pre - y_pre)))) ”
  &&  emp
)

noncomputable def delta_return_wit_1_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre >= y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((x_pre - y_pre) = (Z.abs ((x_pre - y_pre))))

noncomputable def delta_return_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre < y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((y_pre - x_pre) = (Z.abs ((x_pre - y_pre)))) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre < y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((y_pre - x_pre) = (Z.abs ((x_pre - y_pre)))) ”
  &&  emp
)

noncomputable def delta_return_wit_2_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre < y_pre)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : ((0 : Int) <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((y_pre - x_pre) = (Z.abs ((x_pre - y_pre))))


structure VC_Correct : Type where
  proof_of_delta_safety_wit_1 : delta_safety_wit_1
  proof_of_delta_safety_wit_2 : delta_safety_wit_2
  proof_of_delta_return_wit_1 : delta_return_wit_1
  proof_of_delta_return_wit_2 : delta_return_wit_2

end SimpleC.EE.QCP_demos_LLM.generated.delta_goal
