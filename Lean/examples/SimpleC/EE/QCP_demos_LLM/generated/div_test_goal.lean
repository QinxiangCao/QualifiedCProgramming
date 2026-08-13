import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.div_test_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance div_test_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def div_test_safety_wit_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (INT_MIN < c_pre)) (PreH6 : (c_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def div_test_safety_wit_2 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (c_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def div_test_safety_wit_3 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (c_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ (((a_pre * b_pre) ≠ (-9223372036854775808)) ∨ (c_pre ≠ (-1))) ” &&
  “ (c_pre ≠ (0 : Int)) ”

noncomputable def div_test_safety_wit_4 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (c_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((a_pre * b_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (a_pre * b_pre)) ”

noncomputable def div_test_safety_wit_5 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (c_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64 |-> ((Z.quot (a_pre * b_pre) c_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def div_test_safety_wit_6 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (a_pre * b_pre) c_pre) < (0 : Int))) (PreH2 : (c_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64 |-> ((Z.quot (a_pre * b_pre) c_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def div_test_return_wit_1 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (a_pre * b_pre) c_pre) >= (0 : Int))) (PreH2 : (c_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.quot (a_pre * b_pre) c_pre) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int)))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (a_pre * b_pre) c_pre) >= (0 : Int))) (PreH2 : (c_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.quot (a_pre * b_pre) c_pre) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int)))) ”
  &&  emp
)

noncomputable def div_test_return_wit_1_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (a_pre * b_pre) c_pre) >= (0 : Int))) (PreH2 : (c_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((Z.quot (a_pre * b_pre) c_pre) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int))))

noncomputable def div_test_return_wit_2 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (a_pre * b_pre) c_pre) < (0 : Int))) (PreH2 : (c_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int)))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (a_pre * b_pre) c_pre) < (0 : Int))) (PreH2 : (c_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int)))) ”
  &&  emp
)

noncomputable def div_test_return_wit_2_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (a_pre * b_pre) c_pre) < (0 : Int))) (PreH2 : (c_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((0 : Int) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int))))

noncomputable def div_test_return_wit_3 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (c_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int)))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (c_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int)))) ”
  &&  emp
)

noncomputable def div_test_return_wit_3_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (c_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((0 : Int) = (Pos_Div ((a_pre * b_pre)) (c_pre) ((0 : Int))))


structure VC_Correct : Type where
  proof_of_div_test_safety_wit_1 : div_test_safety_wit_1
  proof_of_div_test_safety_wit_2 : div_test_safety_wit_2
  proof_of_div_test_safety_wit_3 : div_test_safety_wit_3
  proof_of_div_test_safety_wit_4 : div_test_safety_wit_4
  proof_of_div_test_safety_wit_5 : div_test_safety_wit_5
  proof_of_div_test_safety_wit_6 : div_test_safety_wit_6
  proof_of_div_test_return_wit_1 : div_test_return_wit_1
  proof_of_div_test_return_wit_2 : div_test_return_wit_2
  proof_of_div_test_return_wit_3 : div_test_return_wit_3

end SimpleC.EE.QCP_demos_LLM.generated.div_test_goal
