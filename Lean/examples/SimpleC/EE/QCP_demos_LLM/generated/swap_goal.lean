import SimpleC.SL.SeparationLogic


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.swap_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance swap_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def swap_return_wit_1_eq : Prop :=
  forall (py_pre : Int) (px_pre : Int) (x_eq : Int) (PreH1 : (px_pre = py_pre)) ,
  ((py_pre) # Int |-> (x_eq))
|--
  ((px_pre) # Int |-> (x_eq))

noncomputable def swap_return_wit_2_neq : Prop :=
  forall (py_pre : Int) (px_pre : Int) (y_neq : Int) (x_neq : Int) ,
  ((px_pre) # Int |-> (y_neq))
  ** ((py_pre) # Int |-> (x_neq))
|--
  ((px_pre) # Int |-> (y_neq))
  ** ((py_pre) # Int |-> (x_neq))

noncomputable def swap_partial_solve_wit_1_eq : Prop :=
  forall (py_pre : Int) (px_pre : Int) (x_eq : Int) (PreH1 : (px_pre = py_pre)) ,
  ((px_pre) # Int |-> (x_eq))
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int |-> (x_eq))

noncomputable def swap_partial_solve_wit_2_eq : Prop :=
  forall (py_pre : Int) (px_pre : Int) (x_eq : Int) (PreH1 : (px_pre = py_pre)) ,
  ((py_pre) # Int |-> (x_eq))
|--
  “ (px_pre = py_pre) ”
  &&  ((px_pre) # Int |->_)

noncomputable def swap_partial_solve_wit_3_eq : Prop :=
  forall (py_pre : Int) (px_pre : Int) (x_eq : Int) (PreH1 : (px_pre = py_pre)) ,
  ((px_pre) # Int |-> (x_eq))
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int |->_)

noncomputable def swap_test1_return_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (x_pre_v_2 : Int) (y_pre_v_2 : Int) (PreH1 : (x_pre ≠ y_pre)) (PreH2 : (x_pre_v_2 = 1)) (PreH3 : (y_pre_v_2 = 2)) ,
  ((x_pre) # Int |-> (y_pre_v_2))
  ** ((y_pre) # Int |-> (x_pre_v_2))
|--
  EX x_pre_v : Int, EX y_pre_v : Int,
  “ (y_pre_v = 1) ” &&
  “ (x_pre_v = 2) ”
  &&  ((y_pre) # Int |-> (y_pre_v))
  ** ((x_pre) # Int |-> (x_pre_v))

noncomputable def swap_test1_partial_solve_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (x_pre_v : Int) (y_pre_v : Int) (PreH1 : (x_pre ≠ y_pre)) (PreH2 : (x_pre_v = 1)) (PreH3 : (y_pre_v = 2)) ,
  ((x_pre) # Int |-> (x_pre_v))
  ** ((y_pre) # Int |-> (y_pre_v))
|--
  “ (x_pre ≠ y_pre) ” &&
  “ (x_pre_v = 1) ” &&
  “ (y_pre_v = 2) ”
  &&  ((x_pre) # Int |-> (x_pre_v))
  ** ((y_pre) # Int |-> (y_pre_v))

noncomputable def swap_test2_return_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (x_pre_v : Int) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre_v = 1)) ,
  ((x_pre) # Int |-> (x_pre_v))
|--
  EX y_pre_v : Int,
  “ (y_pre_v = 1) ”
  &&  ((y_pre) # Int |-> (y_pre_v))

noncomputable def swap_test2_partial_solve_wit_1_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (x_pre_v : Int) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre_v = 1)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> (x_pre_v))
|--
  “ (x_pre = y_pre) ”

noncomputable def swap_test2_partial_solve_wit_1_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (x_pre_v : Int) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre_v = 1)) ,
  ((x_pre) # Int |-> (x_pre_v))
|--
  “ (x_pre = y_pre) ” &&
  “ (x_pre = y_pre) ” &&
  “ (x_pre_v = 1) ”
  &&  ((x_pre) # Int |-> (x_pre_v))

noncomputable def swap_test2_partial_solve_wit_1 : Prop := swap_test2_partial_solve_wit_1_pure -> swap_test2_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_swap_return_wit_1_eq : swap_return_wit_1_eq
  proof_of_swap_return_wit_2_neq : swap_return_wit_2_neq
  proof_of_swap_partial_solve_wit_1_eq : swap_partial_solve_wit_1_eq
  proof_of_swap_partial_solve_wit_2_eq : swap_partial_solve_wit_2_eq
  proof_of_swap_partial_solve_wit_3_eq : swap_partial_solve_wit_3_eq
  proof_of_swap_test1_return_wit_1 : swap_test1_return_wit_1
  proof_of_swap_test1_partial_solve_wit_1 : swap_test1_partial_solve_wit_1
  proof_of_swap_test2_return_wit_1 : swap_test2_return_wit_1
  proof_of_swap_test2_partial_solve_wit_1_pure : swap_test2_partial_solve_wit_1_pure
  proof_of_swap_test2_partial_solve_wit_1 : swap_test2_partial_solve_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.swap_goal
