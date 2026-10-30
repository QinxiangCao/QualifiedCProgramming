import SimpleC.SL.LeanPrinterPrelude


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
open scoped SimpleC.SL.SAC CoqZ

local instance swap_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def swap_return_wit_1_eq : Prop :=
  forall (x_eq : Int) (px_pre : Int) (py_pre : Int) (PreH1 : (px_pre = py_pre)) ,
  ((py_pre) # Int |-> (x_eq))
|--
  ((px_pre) # Int |-> (x_eq))

noncomputable def swap_return_wit_2_neq : Prop :=
  forall (y_neq : Int) (x_neq : Int) (px_pre : Int) (py_pre : Int) ,
  ((px_pre) # Int |-> (y_neq))
  ** ((py_pre) # Int |-> (x_neq))
|--
  ((px_pre) # Int |-> (y_neq))
  ** ((py_pre) # Int |-> (x_neq))

noncomputable def swap_partial_solve_wit_1_eq : Prop :=
  forall (x_eq : Int) (px_pre : Int) (py_pre : Int) (PreH1 : (px_pre = py_pre)) ,
  ((px_pre) # Int |-> (x_eq))
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int |-> (x_eq))

noncomputable def swap_partial_solve_wit_2_eq : Prop :=
  forall (x_eq : Int) (px_pre : Int) (py_pre : Int) (PreH1 : (px_pre = py_pre)) ,
  ((py_pre) # Int |-> (x_eq))
|--
  “ (px_pre = py_pre) ”
  &&  ((px_pre) # Int |->_)

noncomputable def swap_partial_solve_wit_3_eq : Prop :=
  forall (x_eq : Int) (px_pre : Int) (py_pre : Int) (PreH1 : (px_pre = py_pre)) ,
  ((px_pre) # Int |-> (x_eq))
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int |->_)

noncomputable def swap_test1_return_wit_1 : Prop :=
  forall (x_pre : Int) (y_pre : Int) (x_v_2 : Int) (y_v_2 : Int) (PreH1 : (x_pre ≠ y_pre)) (PreH2 : (x_v_2 = 1)) (PreH3 : (y_v_2 = 2)) ,
  ((x_pre) # Int |-> (y_v_2))
  ** ((y_pre) # Int |-> (x_v_2))
|--
  EX x_v : Int, EX y_v : Int,
  “ (y_v = 1) ” &&
  “ (x_v = 2) ”
  &&  ((y_pre) # Int |-> (y_v))
  ** ((x_pre) # Int |-> (x_v))

noncomputable def swap_test1_partial_solve_wit_1 : Prop :=
  forall (x_pre : Int) (y_pre : Int) (x_v : Int) (y_v : Int) (PreH1 : (x_pre ≠ y_pre)) (PreH2 : (x_v = 1)) (PreH3 : (y_v = 2)) ,
  ((x_pre) # Int |-> (x_v))
  ** ((y_pre) # Int |-> (y_v))
|--
  “ (x_pre ≠ y_pre) ” &&
  “ (x_v = 1) ” &&
  “ (y_v = 2) ”
  &&  ((x_pre) # Int |-> (x_v))
  ** ((y_pre) # Int |-> (y_v))

noncomputable def swap_test2_return_wit_1 : Prop :=
  forall (x_pre : Int) (y_pre : Int) (x_v : Int) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_v = 1)) ,
  ((x_pre) # Int |-> (x_v))
|--
  EX y_v : Int,
  “ (y_v = 1) ”
  &&  ((y_pre) # Int |-> (y_v))

noncomputable def swap_test2_partial_solve_wit_1_pure : Prop :=
  forall (x_pre : Int) (y_pre : Int) (x_v : Int) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_v = 1)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> (x_v))
|--
  “ (x_pre = y_pre) ”

noncomputable def swap_test2_partial_solve_wit_1_aux : Prop :=
  forall (x_pre : Int) (y_pre : Int) (x_v : Int) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_v = 1)) ,
  ((x_pre) # Int |-> (x_v))
|--
  “ (x_pre = y_pre) ” &&
  “ (x_pre = y_pre) ” &&
  “ (x_v = 1) ”
  &&  ((x_pre) # Int |-> (x_v))

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
