import SimpleC.SL.SeparationLogic


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.add_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance add_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def add_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 100)) (PreH3 : ((0 : Int) <= y_pre)) (PreH4 : (y_pre <= 100)) ,
  ((( &( "z" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((x_pre + y_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_pre + y_pre)) ”

noncomputable def add_return_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 100)) (PreH3 : ((0 : Int) <= y_pre)) (PreH4 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((x_pre + y_pre) = (x_pre + y_pre)) ”
  &&  emp

noncomputable def slow_add_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (y : Int) (x : Int) (PreH1 : ((0 : Int) <= x)) (PreH2 : (x <= 100)) (PreH3 : ((0 : Int) <= y)) (PreH4 : (y <= 200)) (PreH5 : ((0 : Int) <= x_pre)) (PreH6 : (x_pre <= 100)) (PreH7 : ((0 : Int) <= y_pre)) (PreH8 : (y_pre <= 100)) (PreH9 : ((x + y) = (x_pre + y_pre))) ,
  ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def slow_add_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (y : Int) (x : Int) (PreH1 : (x > (0 : Int))) (PreH2 : ((0 : Int) <= x)) (PreH3 : (x <= 100)) (PreH4 : ((0 : Int) <= y)) (PreH5 : (y <= 200)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 100)) (PreH8 : ((0 : Int) <= y_pre)) (PreH9 : (y_pre <= 100)) (PreH10 : ((x + y) = (x_pre + y_pre))) ,
  ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
|--
  “ ((x - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x - 1)) ”

noncomputable def slow_add_safety_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (y : Int) (x : Int) (PreH1 : (x > (0 : Int))) (PreH2 : ((0 : Int) <= x)) (PreH3 : (x <= 100)) (PreH4 : ((0 : Int) <= y)) (PreH5 : (y <= 200)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 100)) (PreH8 : ((0 : Int) <= y_pre)) (PreH9 : (y_pre <= 100)) (PreH10 : ((x + y) = (x_pre + y_pre))) ,
  ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def slow_add_safety_wit_4 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (y : Int) (x : Int) (PreH1 : (x > (0 : Int))) (PreH2 : ((0 : Int) <= x)) (PreH3 : (x <= 100)) (PreH4 : ((0 : Int) <= y)) (PreH5 : (y <= 200)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 100)) (PreH8 : ((0 : Int) <= y_pre)) (PreH9 : (y_pre <= 100)) (PreH10 : ((x + y) = (x_pre + y_pre))) ,
  ((( &( "x" ) )) # Int |-> ((x - 1)))
  ** ((( &( "y" ) )) # Int |-> (y))
|--
  “ ((y + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (y + 1)) ”

noncomputable def slow_add_safety_wit_5 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (y : Int) (x : Int) (PreH1 : (x > (0 : Int))) (PreH2 : ((0 : Int) <= x)) (PreH3 : (x <= 100)) (PreH4 : ((0 : Int) <= y)) (PreH5 : (y <= 200)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 100)) (PreH8 : ((0 : Int) <= y_pre)) (PreH9 : (y_pre <= 100)) (PreH10 : ((x + y) = (x_pre + y_pre))) ,
  ((( &( "x" ) )) # Int |-> ((x - 1)))
  ** ((( &( "y" ) )) # Int |-> (y))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def slow_add_entail_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 100)) (PreH3 : ((0 : Int) <= y_pre)) (PreH4 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 100) ” &&
  “ ((0 : Int) <= y_pre) ” &&
  “ (y_pre <= 200) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 100) ” &&
  “ ((0 : Int) <= y_pre) ” &&
  “ (y_pre <= 100) ” &&
  “ ((x_pre + y_pre) = (x_pre + y_pre)) ”
  &&  emp

noncomputable def slow_add_entail_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (y : Int) (x : Int) (PreH1 : (x > (0 : Int))) (PreH2 : ((0 : Int) <= x)) (PreH3 : (x <= 100)) (PreH4 : ((0 : Int) <= y)) (PreH5 : (y <= 200)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 100)) (PreH8 : ((0 : Int) <= y_pre)) (PreH9 : (y_pre <= 100)) (PreH10 : ((x + y) = (x_pre + y_pre))) ,
  TT && emp 
|--
  “ ((0 : Int) <= (x - 1)) ” &&
  “ ((x - 1) <= 100) ” &&
  “ ((0 : Int) <= (y + 1)) ” &&
  “ ((y + 1) <= 200) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 100) ” &&
  “ ((0 : Int) <= y_pre) ” &&
  “ (y_pre <= 100) ” &&
  “ (((x - 1) + (y + 1)) = (x_pre + y_pre)) ”
  &&  emp

noncomputable def slow_add_return_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (y : Int) (x : Int) (PreH1 : (x <= (0 : Int))) (PreH2 : ((0 : Int) <= x)) (PreH3 : (x <= 100)) (PreH4 : ((0 : Int) <= y)) (PreH5 : (y <= 200)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 100)) (PreH8 : ((0 : Int) <= y_pre)) (PreH9 : (y_pre <= 100)) (PreH10 : ((x + y) = (x_pre + y_pre))) ,
  TT && emp 
|--
  “ (y = (x_pre + y_pre)) ”
  &&  emp

noncomputable def add1_1_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ ((x_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_pre + 1)) ”

noncomputable def add1_1_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def add1_1_return_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((x_pre + 1) = (x_pre + 1)) ”
  &&  emp

noncomputable def add1_2_safety_wit_1 : Prop :=
  forall (x_pre : Int) (v : Int) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((x_pre) # Int |-> (v))
|--
  “ ((v + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (v + 1)) ”

noncomputable def add1_2_return_wit_1 : Prop :=
  forall (x_pre : Int) (v : Int) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((x_pre) # Int |-> ((v + 1)))
|--
  EX x_pre_v : Int,
  “ (x_pre_v = (v + 1)) ”
  &&  ((x_pre) # Int |-> (x_pre_v))

noncomputable def add1_3_safety_wit_1 : Prop :=
  forall (x_pre : Int) (v : Int) (x_pre_v : Int) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((x_pre) # Ptr |-> (x_pre_v))
  ** ((x_pre_v) # Int |-> (v))
|--
  “ ((v + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (v + 1)) ”

noncomputable def add1_3_safety_wit_2 : Prop :=
  forall (x_pre : Int) (v : Int) (x_pre_v : Int) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((x_pre) # Ptr |-> (x_pre_v))
  ** ((x_pre_v) # Int |-> (v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def add1_3_return_wit_1 : Prop :=
  forall (x_pre : Int) (v : Int) (x_pre_v_2 : Int) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((x_pre) # Ptr |-> (x_pre_v_2))
  ** ((x_pre_v_2) # Int |-> ((v + 1)))
|--
  EX x_pre_v_v : Int, EX x_pre_v : Int,
  “ (x_pre_v_v = (v + 1)) ”
  &&  ((x_pre) # Ptr |-> (x_pre_v))
  ** ((x_pre_v) # Int |-> (x_pre_v_v))


structure VC_Correct : Type where
  proof_of_add_safety_wit_1 : add_safety_wit_1
  proof_of_add_return_wit_1 : add_return_wit_1
  proof_of_slow_add_safety_wit_1 : slow_add_safety_wit_1
  proof_of_slow_add_safety_wit_2 : slow_add_safety_wit_2
  proof_of_slow_add_safety_wit_3 : slow_add_safety_wit_3
  proof_of_slow_add_safety_wit_4 : slow_add_safety_wit_4
  proof_of_slow_add_safety_wit_5 : slow_add_safety_wit_5
  proof_of_slow_add_entail_wit_1 : slow_add_entail_wit_1
  proof_of_slow_add_entail_wit_2 : slow_add_entail_wit_2
  proof_of_slow_add_return_wit_1 : slow_add_return_wit_1
  proof_of_add1_1_safety_wit_1 : add1_1_safety_wit_1
  proof_of_add1_1_safety_wit_2 : add1_1_safety_wit_2
  proof_of_add1_1_return_wit_1 : add1_1_return_wit_1
  proof_of_add1_2_safety_wit_1 : add1_2_safety_wit_1
  proof_of_add1_2_return_wit_1 : add1_2_return_wit_1
  proof_of_add1_3_safety_wit_1 : add1_3_safety_wit_1
  proof_of_add1_3_safety_wit_2 : add1_3_safety_wit_2
  proof_of_add1_3_return_wit_1 : add1_3_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.add_goal
