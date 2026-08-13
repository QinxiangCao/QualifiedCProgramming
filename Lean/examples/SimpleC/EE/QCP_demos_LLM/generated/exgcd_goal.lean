import SimpleC.SL.SeparationLogic


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.exgcd_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance exgcd_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def exgcd_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def exgcd_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def exgcd_safety_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre < (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def exgcd_safety_wit_4 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre < (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def exgcd_safety_wit_5 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre >= (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def exgcd_safety_wit_6 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def exgcd_safety_wit_7 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def exgcd_safety_wit_8 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre < (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> ((-1)))
  ** ((y_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def exgcd_safety_wit_9 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> ((0 : Int)))
  ** ((y_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def exgcd_safety_wit_10 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> (1))
  ** ((y_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def exgcd_safety_wit_11 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ ((a_pre ≠ (INT_MIN)) ∨ (b_pre ≠ (-1))) ” &&
  “ (b_pre ≠ (0 : Int)) ”

noncomputable def exgcd_safety_wit_12 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))) ”

noncomputable def exgcd_safety_wit_13 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ (((Z.quot a_pre b_pre) * y_callee_v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot a_pre b_pre) * y_callee_v)) ”

noncomputable def exgcd_safety_wit_14 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((a_pre ≠ (INT_MIN)) ∨ (b_pre ≠ (-1))) ” &&
  “ (b_pre ≠ (0 : Int)) ”

noncomputable def exgcd_safety_wit_15 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))) ”
)

noncomputable def exgcd_safety_wit_15_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)) <= INT_MAX) ”

noncomputable def exgcd_safety_wit_15_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((INT_MIN) <= (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))) ”

noncomputable def exgcd_safety_wit_16 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ (((Z.quot a_pre b_pre) * y_callee_v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot a_pre b_pre) * y_callee_v)) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ (((Z.quot a_pre b_pre) * y_callee_v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot a_pre b_pre) * y_callee_v)) ”
)

noncomputable def exgcd_safety_wit_16_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ (((Z.quot a_pre b_pre) * y_callee_v) <= INT_MAX) ”

noncomputable def exgcd_safety_wit_16_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((INT_MIN) <= ((Z.quot a_pre b_pre) * y_callee_v)) ”

noncomputable def exgcd_safety_wit_17 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((a_pre ≠ (INT_MIN)) ∨ (b_pre ≠ (-1))) ” &&
  “ (b_pre ≠ (0 : Int)) ”

noncomputable def exgcd_safety_wit_18 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))) ”
)

noncomputable def exgcd_safety_wit_18_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)) <= INT_MAX) ”

noncomputable def exgcd_safety_wit_18_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((INT_MIN) <= (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))) ”

noncomputable def exgcd_safety_wit_19 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ (((Z.quot a_pre b_pre) * y_callee_v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot a_pre b_pre) * y_callee_v)) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ (((Z.quot a_pre b_pre) * y_callee_v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot a_pre b_pre) * y_callee_v)) ”
)

noncomputable def exgcd_safety_wit_19_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ (((Z.quot a_pre b_pre) * y_callee_v) <= INT_MAX) ”

noncomputable def exgcd_safety_wit_19_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((INT_MIN) <= ((Z.quot a_pre b_pre) * y_callee_v)) ”

noncomputable def exgcd_safety_wit_20 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> (x_callee_v))
  ** ((x_pre) # Int |-> (y_callee_v))
  ** ((( &( "g" ) )) # Int |-> (retval))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
|--
  “ ((a_pre ≠ (INT_MIN)) ∨ (b_pre ≠ (-1))) ” &&
  “ (b_pre ≠ (0 : Int)) ”

noncomputable def exgcd_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))))
  ** ((x_pre) # Int |-> (y_callee_v))
|--
  EX y_pre_v_2 : Int, EX x_pre_v_2 : Int,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_pre_v_2) + (b_pre * y_pre_v_2)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre ≠ (0 : Int)) ” &&
  “ ((Z.rem a_pre b_pre) = (0 : Int)) ” &&
  “ (x_pre_v_2 = (0 : Int)) ” &&
  “ ((Zabs (y_pre_v_2)) <= 1) ”
  &&  ((x_pre) # Int |-> (x_pre_v_2))
  ** ((y_pre) # Int |-> (y_pre_v_2))
) \/
(
forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) <= 1) ” &&
  “ (((a_pre * (0 : Int)) + (b_pre * (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def exgcd_return_wit_1_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  ((Zabs ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) <= 1)

noncomputable def exgcd_return_wit_1_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  (((a_pre * (0 : Int)) + (b_pre * (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_1_split_goal_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) = (0 : Int))) (PreH4 : ((Zabs (x_callee_v)) <= 1)) (PreH5 : (y_callee_v = (0 : Int))) (PreH6 : (b_pre ≠ (0 : Int))) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))))
  ** ((x_pre) # Int |-> (y_callee_v))
|--
  EX y_pre_v_3 : Int, EX x_pre_v_3 : Int,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_pre_v_3) + (b_pre * y_pre_v_3)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre ≠ (0 : Int)) ” &&
  “ ((Z.rem a_pre b_pre) ≠ (0 : Int)) ” &&
  “ ((Zabs (x_pre_v_3)) <= (Z.quot (Zabs (b_pre)) (Zgcd (a_pre) (b_pre)))) ” &&
  “ ((Zabs (y_pre_v_3)) <= (Z.quot (Zabs (a_pre)) (Zgcd (a_pre) (b_pre)))) ”
  &&  ((x_pre) # Int |-> (x_pre_v_3))
  ** ((y_pre) # Int |-> (y_pre_v_3))
) \/
(
forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) <= (Z.quot (Zabs (a_pre)) (Zgcd (a_pre) (b_pre)))) ” &&
  “ ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (a_pre) (b_pre)))) ” &&
  “ (((a_pre * y_callee_v) + (b_pre * (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def exgcd_return_wit_2_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) <= (Z.quot (Zabs (a_pre)) (Zgcd (a_pre) (b_pre))))

noncomputable def exgcd_return_wit_2_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (a_pre) (b_pre))))

noncomputable def exgcd_return_wit_2_split_goal_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (((a_pre * y_callee_v) + (b_pre * (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_2_split_goal_4 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) = (0 : Int))) (PreH5 : (x_callee_v = (0 : Int))) (PreH6 : ((Zabs (y_callee_v)) <= 1)) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_3 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((y_pre) # Int |-> ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v))))
  ** ((x_pre) # Int |-> (y_callee_v))
|--
  EX y_pre_v_3 : Int, EX x_pre_v_3 : Int,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_pre_v_3) + (b_pre * y_pre_v_3)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre ≠ (0 : Int)) ” &&
  “ ((Z.rem a_pre b_pre) ≠ (0 : Int)) ” &&
  “ ((Zabs (x_pre_v_3)) <= (Z.quot (Zabs (b_pre)) (Zgcd (a_pre) (b_pre)))) ” &&
  “ ((Zabs (y_pre_v_3)) <= (Z.quot (Zabs (a_pre)) (Zgcd (a_pre) (b_pre)))) ”
  &&  ((x_pre) # Int |-> (x_pre_v_3))
  ** ((y_pre) # Int |-> (y_pre_v_3))
) \/
(
forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) <= (Z.quot (Zabs (a_pre)) (Zgcd (a_pre) (b_pre)))) ” &&
  “ ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (a_pre) (b_pre)))) ” &&
  “ (((a_pre * y_callee_v) + (b_pre * (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def exgcd_return_wit_3_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs ((x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) <= (Z.quot (Zabs (a_pre)) (Zgcd (a_pre) (b_pre))))

noncomputable def exgcd_return_wit_3_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (a_pre) (b_pre))))

noncomputable def exgcd_return_wit_3_split_goal_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (((a_pre * y_callee_v) + (b_pre * (x_callee_v - ((Z.quot a_pre b_pre) * y_callee_v)))) = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_3_split_goal_4 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : (retval = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH2 : (((b_pre * x_callee_v) + ((Z.rem a_pre b_pre) * y_callee_v)) = (Zgcd (b_pre) ((Z.rem a_pre b_pre))))) (PreH3 : ((Z.rem a_pre b_pre) ≠ (0 : Int))) (PreH4 : ((Z.rem b_pre (Z.rem a_pre b_pre)) ≠ (0 : Int))) (PreH5 : ((Zabs (x_callee_v)) <= (Z.quot (Zabs ((Z.rem a_pre b_pre))) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH6 : ((Zabs (y_callee_v)) <= (Z.quot (Zabs (b_pre)) (Zgcd (b_pre) ((Z.rem a_pre b_pre)))))) (PreH7 : (b_pre ≠ (0 : Int))) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_4 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int |-> ((-1)))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  EX y_pre_v : Int, EX x_pre_v : Int,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_pre_v) + (b_pre * y_pre_v)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre = (0 : Int)) ” &&
  “ ((Zabs (x_pre_v)) <= 1) ” &&
  “ (y_pre_v = (0 : Int)) ”
  &&  ((x_pre) # Int |-> (x_pre_v))
  ** ((y_pre) # Int |-> (y_pre_v))
) \/
(
forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((-1))) <= 1) ” &&
  “ (((a_pre * (-1)) + (b_pre * (0 : Int))) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def exgcd_return_wit_4_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((Zabs ((-1))) <= 1)

noncomputable def exgcd_return_wit_4_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  (((a_pre * (-1)) + (b_pre * (0 : Int))) = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_4_split_goal_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre < (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_5 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int |-> ((0 : Int)))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  EX y_pre_v : Int, EX x_pre_v : Int,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_pre_v) + (b_pre * y_pre_v)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre = (0 : Int)) ” &&
  “ ((Zabs (x_pre_v)) <= 1) ” &&
  “ (y_pre_v = (0 : Int)) ”
  &&  ((x_pre) # Int |-> (x_pre_v))
  ** ((y_pre) # Int |-> (y_pre_v))
) \/
(
forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs ((0 : Int))) <= 1) ” &&
  “ (((a_pre * (0 : Int)) + (b_pre * (0 : Int))) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def exgcd_return_wit_5_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((Zabs ((0 : Int))) <= 1)

noncomputable def exgcd_return_wit_5_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (((a_pre * (0 : Int)) + (b_pre * (0 : Int))) = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_5_split_goal_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre = (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_6 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int |-> (1))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  EX y_pre_v : Int, EX x_pre_v : Int,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_pre_v) + (b_pre * y_pre_v)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre = (0 : Int)) ” &&
  “ ((Zabs (x_pre_v)) <= 1) ” &&
  “ (y_pre_v = (0 : Int)) ”
  &&  ((x_pre) # Int |-> (x_pre_v))
  ** ((y_pre) # Int |-> (y_pre_v))
) \/
(
forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zabs (1)) <= 1) ” &&
  “ (((a_pre * 1) + (b_pre * (0 : Int))) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def exgcd_return_wit_6_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  ((Zabs (1)) <= 1)

noncomputable def exgcd_return_wit_6_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (((a_pre * 1) + (b_pre * (0 : Int))) = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_return_wit_6_split_goal_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (retval : Int) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (a_pre >= (0 : Int))) (PreH4 : (b_pre = (0 : Int))) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))

noncomputable def exgcd_partial_solve_wit_1_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre < (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> ((-1)))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ”

noncomputable def exgcd_partial_solve_wit_1_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre < (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int |-> ((-1)))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (a_pre < (0 : Int)) ” &&
  “ (b_pre = (0 : Int)) ” &&
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int |-> ((-1)))
  ** ((y_pre) # Int |-> ((0 : Int)))

noncomputable def exgcd_partial_solve_wit_1 : Prop := exgcd_partial_solve_wit_1_pure -> exgcd_partial_solve_wit_1_aux

noncomputable def exgcd_partial_solve_wit_2_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> ((0 : Int)))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ”

noncomputable def exgcd_partial_solve_wit_2_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int |-> ((0 : Int)))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (a_pre = (0 : Int)) ” &&
  “ (a_pre >= (0 : Int)) ” &&
  “ (b_pre = (0 : Int)) ” &&
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int |-> ((0 : Int)))
  ** ((y_pre) # Int |-> ((0 : Int)))

noncomputable def exgcd_partial_solve_wit_2 : Prop := exgcd_partial_solve_wit_2_pure -> exgcd_partial_solve_wit_2_aux

noncomputable def exgcd_partial_solve_wit_3_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |-> (1))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ”

noncomputable def exgcd_partial_solve_wit_3_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (a_pre >= (0 : Int))) (PreH3 : (b_pre = (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int |-> (1))
  ** ((y_pre) # Int |-> ((0 : Int)))
|--
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (a_pre ≠ (0 : Int)) ” &&
  “ (a_pre >= (0 : Int)) ” &&
  “ (b_pre = (0 : Int)) ” &&
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int |-> (1))
  ** ((y_pre) # Int |-> ((0 : Int)))

noncomputable def exgcd_partial_solve_wit_3 : Prop := exgcd_partial_solve_wit_3_pure -> exgcd_partial_solve_wit_3_aux

noncomputable def exgcd_partial_solve_wit_4_pure : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ” &&
  “ ((Z.rem a_pre b_pre) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.rem a_pre b_pre)) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre >= INT_MIN)) (PreH2 : (a_pre >= INT_MIN)) (PreH3 : (b_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ (INT_MIN < (Z.rem a_pre b_pre)) ” &&
  “ ((Z.rem a_pre b_pre) <= INT_MAX) ”
)

noncomputable def exgcd_partial_solve_wit_4_pure_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre >= INT_MIN)) (PreH2 : (a_pre >= INT_MIN)) (PreH3 : (b_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ (INT_MIN < (Z.rem a_pre b_pre)) ”

noncomputable def exgcd_partial_solve_wit_4_pure_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre >= INT_MIN)) (PreH2 : (a_pre >= INT_MIN)) (PreH3 : (b_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "g" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ ((Z.rem a_pre b_pre) <= INT_MAX) ”

noncomputable def exgcd_partial_solve_wit_4_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (b_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_)
|--
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ” &&
  “ ((Z.rem a_pre b_pre) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.rem a_pre b_pre)) ” &&
  “ (b_pre ≠ (0 : Int)) ” &&
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ”
  &&  ((y_pre) # Int |->_)
  ** ((x_pre) # Int |->_)

noncomputable def exgcd_partial_solve_wit_4 : Prop := exgcd_partial_solve_wit_4_pure -> exgcd_partial_solve_wit_4_aux

noncomputable def exgcd_derive_Inter_by_Proof : Prop :=
  forall (y_pre : Int) (x_pre : Int) (b_pre : Int) (a_pre : Int) ,
  (“ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_))
|--
  (“ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ”
  &&  ((x_pre) # Int |->_)
  ** ((y_pre) # Int |->_))
  **
  (((EX y_callee_v : Int, EX x_callee_v : Int, EX retval_2 : Int,
  “ (retval_2 = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_callee_v) + (b_pre * y_callee_v)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre = (0 : Int)) ” &&
  “ ((Zabs (x_callee_v)) <= 1) ” &&
  “ (y_callee_v = (0 : Int)) ”
  &&  ((x_pre) # Int |-> (x_callee_v))
  ** ((y_pre) # Int |-> (y_callee_v)))
  ||
  (EX y_callee_v_2 : Int, EX x_callee_v_2 : Int, EX retval_2 : Int,
  “ (retval_2 = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_callee_v_2) + (b_pre * y_callee_v_2)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre ≠ (0 : Int)) ” &&
  “ ((Z.rem a_pre b_pre) = (0 : Int)) ” &&
  “ (x_callee_v_2 = (0 : Int)) ” &&
  “ ((Zabs (y_callee_v_2)) <= 1) ”
  &&  ((x_pre) # Int |-> (x_callee_v_2))
  ** ((y_pre) # Int |-> (y_callee_v_2)))
  ||
  (EX y_callee_v_3 : Int, EX x_callee_v_3 : Int, EX retval_2 : Int,
  “ (retval_2 = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_callee_v_3) + (b_pre * y_callee_v_3)) = (Zgcd (a_pre) (b_pre))) ” &&
  “ (b_pre ≠ (0 : Int)) ” &&
  “ ((Z.rem a_pre b_pre) ≠ (0 : Int)) ” &&
  “ ((Zabs (x_callee_v_3)) <= (Z.quot (Zabs (b_pre)) (Zgcd (a_pre) (b_pre)))) ” &&
  “ ((Zabs (y_callee_v_3)) <= (Z.quot (Zabs (a_pre)) (Zgcd (a_pre) (b_pre)))) ”
  &&  ((x_pre) # Int |-> (x_callee_v_3))
  ** ((y_pre) # Int |-> (y_callee_v_3))))
  -*
  (EX y_pre_v : Int, EX x_pre_v : Int, EX retval : Int,
  “ (retval = (Zgcd (a_pre) (b_pre))) ” &&
  “ (((a_pre * x_pre_v) + (b_pre * y_pre_v)) = (Zgcd (a_pre) (b_pre))) ”
  &&  ((x_pre) # Int |-> (x_pre_v))
  ** ((y_pre) # Int |-> (y_pre_v))))


structure VC_Correct : Type where
  proof_of_exgcd_safety_wit_1 : exgcd_safety_wit_1
  proof_of_exgcd_safety_wit_2 : exgcd_safety_wit_2
  proof_of_exgcd_safety_wit_3 : exgcd_safety_wit_3
  proof_of_exgcd_safety_wit_4 : exgcd_safety_wit_4
  proof_of_exgcd_safety_wit_5 : exgcd_safety_wit_5
  proof_of_exgcd_safety_wit_6 : exgcd_safety_wit_6
  proof_of_exgcd_safety_wit_7 : exgcd_safety_wit_7
  proof_of_exgcd_safety_wit_8 : exgcd_safety_wit_8
  proof_of_exgcd_safety_wit_9 : exgcd_safety_wit_9
  proof_of_exgcd_safety_wit_10 : exgcd_safety_wit_10
  proof_of_exgcd_safety_wit_11 : exgcd_safety_wit_11
  proof_of_exgcd_safety_wit_12 : exgcd_safety_wit_12
  proof_of_exgcd_safety_wit_13 : exgcd_safety_wit_13
  proof_of_exgcd_safety_wit_14 : exgcd_safety_wit_14
  proof_of_exgcd_safety_wit_17 : exgcd_safety_wit_17
  proof_of_exgcd_safety_wit_20 : exgcd_safety_wit_20
  proof_of_exgcd_partial_solve_wit_1_pure : exgcd_partial_solve_wit_1_pure
  proof_of_exgcd_partial_solve_wit_1 : exgcd_partial_solve_wit_1
  proof_of_exgcd_partial_solve_wit_2_pure : exgcd_partial_solve_wit_2_pure
  proof_of_exgcd_partial_solve_wit_2 : exgcd_partial_solve_wit_2
  proof_of_exgcd_partial_solve_wit_3_pure : exgcd_partial_solve_wit_3_pure
  proof_of_exgcd_partial_solve_wit_3 : exgcd_partial_solve_wit_3
  proof_of_exgcd_partial_solve_wit_4 : exgcd_partial_solve_wit_4
  proof_of_exgcd_safety_wit_15 : exgcd_safety_wit_15
  proof_of_exgcd_safety_wit_16 : exgcd_safety_wit_16
  proof_of_exgcd_safety_wit_18 : exgcd_safety_wit_18
  proof_of_exgcd_safety_wit_19 : exgcd_safety_wit_19
  proof_of_exgcd_return_wit_1 : exgcd_return_wit_1
  proof_of_exgcd_return_wit_2 : exgcd_return_wit_2
  proof_of_exgcd_return_wit_3 : exgcd_return_wit_3
  proof_of_exgcd_return_wit_4 : exgcd_return_wit_4
  proof_of_exgcd_return_wit_5 : exgcd_return_wit_5
  proof_of_exgcd_return_wit_6 : exgcd_return_wit_6
  proof_of_exgcd_partial_solve_wit_4_pure : exgcd_partial_solve_wit_4_pure
  proof_of_exgcd_derive_Inter_by_Proof : exgcd_derive_Inter_by_Proof

end SimpleC.EE.QCP_demos_LLM.generated.exgcd_goal
