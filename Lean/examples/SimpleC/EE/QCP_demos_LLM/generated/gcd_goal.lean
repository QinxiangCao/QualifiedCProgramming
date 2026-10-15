import SimpleC.SL.LeanPrinterPrelude


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.gcd_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance gcd_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def gcd_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (y_pre <= INT_MAX)) (PreH3 : (y_pre >= INT_MIN)) (PreH4 : (INT_MIN < x_pre)) (PreH5 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def gcd_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (y_pre ≠ (0 : Int))) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((x_pre ≠ (INT_MIN)) ∨ (y_pre ≠ (-1))) ” &&
  “ (y_pre ≠ (0 : Int)) ”

noncomputable def gcd_entail_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (x_pre <= INT_MAX) ” &&
  “ (y_pre <= INT_MAX) ” &&
  “ (y_pre >= INT_MIN) ” &&
  “ (INT_MIN < x_pre) ” &&
  “ (INT_MIN < y_pre) ”
  &&  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))

noncomputable def gcd_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (retval : Int) (PreH1 : (retval = (Zgcd (y_pre) ((Z.rem x_pre y_pre))))) (PreH2 : (y_pre ≠ (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) (y_pre))) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (retval : Int) (PreH1 : (retval = (Zgcd (y_pre) ((Z.rem x_pre y_pre))))) (PreH2 : (y_pre ≠ (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) (y_pre))) ”
  &&  emp
)

noncomputable def gcd_return_wit_1_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (retval : Int) (PreH1 : (retval = (Zgcd (y_pre) ((Z.rem x_pre y_pre))))) (PreH2 : (y_pre ≠ (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  (retval = (Zgcd (x_pre) (y_pre)))

noncomputable def gcd_return_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (y_pre = (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) (y_pre))) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (y_pre = (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) ((0 : Int)))) ”
  &&  emp
)

noncomputable def gcd_return_wit_2_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (y_pre = (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  (retval = (Zgcd (x_pre) ((0 : Int))))

noncomputable def gcd_partial_solve_wit_1_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (y_pre = (0 : Int))) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (INT_MIN < x_pre) ” &&
  “ (x_pre <= INT_MAX) ”

noncomputable def gcd_partial_solve_wit_1_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (y_pre = (0 : Int))) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (y_pre = (0 : Int)) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (y_pre <= INT_MAX) ” &&
  “ (y_pre >= INT_MIN) ” &&
  “ (INT_MIN < x_pre) ” &&
  “ (INT_MIN < y_pre) ”
  &&  emp

noncomputable def gcd_partial_solve_wit_1 : Prop := gcd_partial_solve_wit_1_pure -> gcd_partial_solve_wit_1_aux

noncomputable def gcd_partial_solve_wit_2_pure : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (PreH1 : (y_pre ≠ (0 : Int))) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (INT_MIN < y_pre) ” &&
  “ (INT_MIN < (Z.rem x_pre y_pre)) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre >= INT_MIN)) (PreH2 : (y_pre ≠ (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (INT_MIN < (Z.rem x_pre y_pre)) ”
)

noncomputable def gcd_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre >= INT_MIN)) (PreH2 : (y_pre ≠ (0 : Int))) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (INT_MIN < (Z.rem x_pre y_pre)) ”

noncomputable def gcd_partial_solve_wit_2_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (y_pre ≠ (0 : Int))) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)) ,
  TT && emp 
|--
  “ (INT_MIN < y_pre) ” &&
  “ (INT_MIN < (Z.rem x_pre y_pre)) ” &&
  “ (y_pre ≠ (0 : Int)) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (y_pre <= INT_MAX) ” &&
  “ (y_pre >= INT_MIN) ” &&
  “ (INT_MIN < x_pre) ” &&
  “ (INT_MIN < y_pre) ”
  &&  emp

noncomputable def gcd_partial_solve_wit_2 : Prop := gcd_partial_solve_wit_2_pure -> gcd_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_gcd_safety_wit_1 : gcd_safety_wit_1
  proof_of_gcd_safety_wit_2 : gcd_safety_wit_2
  proof_of_gcd_entail_wit_1 : gcd_entail_wit_1
  proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure
  proof_of_gcd_partial_solve_wit_1 : gcd_partial_solve_wit_1
  proof_of_gcd_partial_solve_wit_2 : gcd_partial_solve_wit_2
  proof_of_gcd_return_wit_1 : gcd_return_wit_1
  proof_of_gcd_return_wit_2 : gcd_return_wit_2
  proof_of_gcd_partial_solve_wit_2_pure : gcd_partial_solve_wit_2_pure

end SimpleC.EE.QCP_demos_LLM.generated.gcd_goal
