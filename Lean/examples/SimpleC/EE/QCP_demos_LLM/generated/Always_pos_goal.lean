import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.simple_arith.Apos_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.Always_pos_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance Always_pos_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def Always_positive_simple_safety_wit_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (INT_MIN < c_pre)) (PreH6 : (c_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_simple_safety_wit_2 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_simple_safety_wit_3 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |->_)
  ** ((( &( "delta1" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ (((b_pre * b_pre) ≠ (-9223372036854775808)) ∨ (4 ≠ (-1))) ” &&
  “ (4 ≠ (0 : Int)) ”

noncomputable def Always_positive_simple_safety_wit_4 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |->_)
  ** ((( &( "delta1" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((b_pre * b_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (b_pre * b_pre)) ”

noncomputable def Always_positive_simple_safety_wit_5 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |->_)
  ** ((( &( "delta1" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ (4 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 4) ”

noncomputable def Always_positive_simple_safety_wit_6 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |->_)
  ** ((( &( "delta1" ) )) # Int64 |-> ((Z.quot (b_pre * b_pre) 4)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((a_pre * c_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (a_pre * c_pre)) ”

noncomputable def Always_positive_simple_safety_wit_7 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (b_pre * b_pre) 4) >= (a_pre * c_pre))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((Z.quot (b_pre * b_pre) 4)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_simple_safety_wit_8 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((Z.quot (b_pre * b_pre) 4)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_simple_safety_wit_9 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((Z.quot (b_pre * b_pre) 4)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def Always_positive_simple_safety_wit_10 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((Z.quot (b_pre * b_pre) 4)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_simple_return_wit_1 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_simple_return_wit_1_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_simple_return_wit_2 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_simple_return_wit_2_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : ((Z.quot (b_pre * b_pre) 4) < (a_pre * c_pre))) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  (1 = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_simple_return_wit_3 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (b_pre * b_pre) 4) >= (a_pre * c_pre))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (b_pre * b_pre) 4) >= (a_pre * c_pre))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_simple_return_wit_3_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((Z.quot (b_pre * b_pre) 4) >= (a_pre * c_pre))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_simple_return_wit_4 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_simple_return_wit_4_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_safety_wit_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (INT_MIN < c_pre)) (PreH6 : (c_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_2 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_3 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "delta2" ) )) # Int64 |->_)
  ** ((( &( "delta1" ) )) # Int64 |->_)
  ** ((( &( "delta0" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((b_pre * b_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (b_pre * b_pre)) ”

noncomputable def Always_positive_safety_wit_4 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "delta2" ) )) # Int64 |->_)
  ** ((( &( "delta1" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "delta0" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((a_pre * c_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (a_pre * c_pre)) ”

noncomputable def Always_positive_safety_wit_5 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre ≠ (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "delta0" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_6 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) <= (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "delta0" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_7 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) > (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "delta0" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ (4 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 4) ”

noncomputable def Always_positive_safety_wit_8 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (delta2 <= delta1)) (PreH2 : ((0 : Int) < d)) (PreH3 : (d <= 4)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) (PreH10 : ((0 : Int) < (a_pre * c_pre))) (PreH11 : (delta0 = (b_pre * b_pre))) (PreH12 : (delta2 = (a_pre * c_pre))) (PreH13 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> (delta1))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((delta1 - delta2) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (delta1 - delta2)) ”

noncomputable def Always_positive_safety_wit_9 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (delta2 <= delta1)) (PreH2 : ((0 : Int) < d)) (PreH3 : (d <= 4)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) (PreH10 : ((0 : Int) < (a_pre * c_pre))) (PreH11 : (delta0 = (b_pre * b_pre))) (PreH12 : (delta2 = (a_pre * c_pre))) (PreH13 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((d - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (d - 1)) ”

noncomputable def Always_positive_safety_wit_10 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (delta2 <= delta1)) (PreH2 : ((0 : Int) < d)) (PreH3 : (d <= 4)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) (PreH10 : ((0 : Int) < (a_pre * c_pre))) (PreH11 : (delta0 = (b_pre * b_pre))) (PreH12 : (delta2 = (a_pre * c_pre))) (PreH13 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def Always_positive_safety_wit_11 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (delta2 <= delta1)) (PreH2 : ((0 : Int) < d)) (PreH3 : (d <= 4)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) (PreH10 : ((0 : Int) < (a_pre * c_pre))) (PreH11 : (delta0 = (b_pre * b_pre))) (PreH12 : (delta2 = (a_pre * c_pre))) (PreH13 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> ((d - 1)))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_12 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((d - 1) = (0 : Int))) (PreH2 : (delta2 <= delta1)) (PreH3 : ((0 : Int) < d)) (PreH4 : (d <= 4)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) (PreH9 : (INT_MIN < c_pre)) (PreH10 : (c_pre <= INT_MAX)) (PreH11 : ((0 : Int) < (a_pre * c_pre))) (PreH12 : (delta0 = (b_pre * b_pre))) (PreH13 : (delta2 = (a_pre * c_pre))) (PreH14 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> ((d - 1)))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_13 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((delta1 - delta2) < (0 : Int))) (PreH2 : ((d - 1) = (0 : Int))) (PreH3 : (delta2 <= delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> ((d - 1)))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ False ”

noncomputable def Always_positive_safety_wit_14 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((delta1 - delta2) >= (0 : Int))) (PreH2 : ((d - 1) = (0 : Int))) (PreH3 : (delta2 <= delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> ((d - 1)))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_15 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) <= (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "delta0" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_16 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (delta2 > delta1)) (PreH2 : ((0 : Int) < d)) (PreH3 : (d <= 4)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) (PreH10 : ((0 : Int) < (a_pre * c_pre))) (PreH11 : (delta0 = (b_pre * b_pre))) (PreH12 : (delta2 = (a_pre * c_pre))) (PreH13 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> (delta1))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_17 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((delta1 - delta2) >= (0 : Int))) (PreH2 : ((d - 1) = (0 : Int))) (PreH3 : (delta2 <= delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_18 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (d = (0 : Int))) (PreH2 : (delta2 > delta1)) (PreH3 : ((0 : Int) < d)) (PreH4 : (d <= 4)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) (PreH9 : (INT_MIN < c_pre)) (PreH10 : (c_pre <= INT_MAX)) (PreH11 : ((0 : Int) < (a_pre * c_pre))) (PreH12 : (delta0 = (b_pre * b_pre))) (PreH13 : (delta2 = (a_pre * c_pre))) (PreH14 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> (delta1))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ False ”

noncomputable def Always_positive_safety_wit_19 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) <= (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "delta2" ) )) # Int64 |-> ((a_pre * c_pre)))
  ** ((( &( "delta1" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "delta0" ) )) # Int64 |-> ((b_pre * b_pre)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_20 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((delta1 - delta2) >= (0 : Int))) (PreH2 : ((d - 1) = (0 : Int))) (PreH3 : (delta2 <= delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> ((delta1 - delta2)))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_21 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (d ≠ (0 : Int))) (PreH2 : (delta2 > delta1)) (PreH3 : ((0 : Int) < d)) (PreH4 : (d <= 4)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) (PreH9 : (INT_MIN < c_pre)) (PreH10 : (c_pre <= INT_MAX)) (PreH11 : ((0 : Int) < (a_pre * c_pre))) (PreH12 : (delta0 = (b_pre * b_pre))) (PreH13 : (delta2 = (a_pre * c_pre))) (PreH14 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> (delta1))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_safety_wit_22 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> (delta1))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def Always_positive_safety_wit_23 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "delta0" ) )) # Int64 |-> (delta0))
  ** ((( &( "delta2" ) )) # Int64 |-> (delta2))
  ** ((( &( "delta1" ) )) # Int64 |-> (delta1))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "c" ) )) # Int |-> (c_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def Always_positive_entail_wit_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) > (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) < 4) ” &&
  “ (4 <= 4) ” &&
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ” &&
  “ (INT_MIN < c_pre) ” &&
  “ (c_pre <= INT_MAX) ” &&
  “ ((0 : Int) < (a_pre * c_pre)) ” &&
  “ ((b_pre * b_pre) = (b_pre * b_pre)) ” &&
  “ ((a_pre * c_pre) = (a_pre * c_pre)) ” &&
  “ ((b_pre * b_pre) = ((b_pre * b_pre) + ((4 - 4) * (a_pre * c_pre)))) ”
  &&  emp

noncomputable def Always_positive_entail_wit_2 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((d - 1) ≠ (0 : Int))) (PreH2 : (delta2 <= delta1)) (PreH3 : ((0 : Int) < d)) (PreH4 : (d <= 4)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) (PreH9 : (INT_MIN < c_pre)) (PreH10 : (c_pre <= INT_MAX)) (PreH11 : ((0 : Int) < (a_pre * c_pre))) (PreH12 : (delta0 = (b_pre * b_pre))) (PreH13 : (delta2 = (a_pre * c_pre))) (PreH14 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ ((0 : Int) < (d - 1)) ” &&
  “ ((d - 1) <= 4) ” &&
  “ (INT_MIN < a_pre) ” &&
  “ (a_pre <= INT_MAX) ” &&
  “ (INT_MIN < b_pre) ” &&
  “ (b_pre <= INT_MAX) ” &&
  “ (INT_MIN < c_pre) ” &&
  “ (c_pre <= INT_MAX) ” &&
  “ ((0 : Int) < (a_pre * c_pre)) ” &&
  “ (delta0 = (b_pre * b_pre)) ” &&
  “ (delta2 = (a_pre * c_pre)) ” &&
  “ (delta0 = ((delta1 - delta2) + ((4 - (d - 1)) * delta2))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((d - 1) ≠ (0 : Int))) (PreH2 : (delta2 <= delta1)) (PreH3 : ((0 : Int) < d)) (PreH4 : (d <= 4)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) (PreH9 : (INT_MIN < c_pre)) (PreH10 : (c_pre <= INT_MAX)) (PreH11 : ((0 : Int) < (a_pre * c_pre))) (PreH12 : (delta0 = (b_pre * b_pre))) (PreH13 : (delta2 = (a_pre * c_pre))) (PreH14 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ (delta0 = ((delta1 - delta2) + ((4 - (d - 1)) * delta2))) ”
  &&  emp
)

noncomputable def Always_positive_entail_wit_2_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((d - 1) ≠ (0 : Int))) (PreH2 : (delta2 <= delta1)) (PreH3 : ((0 : Int) < d)) (PreH4 : (d <= 4)) (PreH5 : (INT_MIN < a_pre)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (INT_MIN < b_pre)) (PreH8 : (b_pre <= INT_MAX)) (PreH9 : (INT_MIN < c_pre)) (PreH10 : (c_pre <= INT_MAX)) (PreH11 : ((0 : Int) < (a_pre * c_pre))) (PreH12 : (delta0 = (b_pre * b_pre))) (PreH13 : (delta2 = (a_pre * c_pre))) (PreH14 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  (delta0 = ((delta1 - delta2) + ((4 - (d - 1)) * delta2)))

noncomputable def Always_positive_return_wit_1 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_return_wit_1_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre <= (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_return_wit_2 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_return_wit_2_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : (a_pre > (0 : Int))) (PreH2 : (d ≠ (0 : Int))) (PreH3 : (delta2 > delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  (1 = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_return_wit_3 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) <= (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) <= (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_return_wit_3_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((a_pre * c_pre) <= (0 : Int))) (PreH2 : (a_pre ≠ (0 : Int))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_return_wit_4 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((delta1 - delta2) >= (0 : Int))) (PreH2 : ((d - 1) = (0 : Int))) (PreH3 : (delta2 <= delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((delta1 - delta2) >= (0 : Int))) (PreH2 : ((d - 1) = (0 : Int))) (PreH3 : (delta2 <= delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_return_wit_4_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (delta1 : Int) (delta2 : Int) (delta0 : Int) (d : Int) (PreH1 : ((delta1 - delta2) >= (0 : Int))) (PreH2 : ((d - 1) = (0 : Int))) (PreH3 : (delta2 <= delta1)) (PreH4 : ((0 : Int) < d)) (PreH5 : (d <= 4)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (INT_MIN < c_pre)) (PreH11 : (c_pre <= INT_MAX)) (PreH12 : ((0 : Int) < (a_pre * c_pre))) (PreH13 : (delta0 = (b_pre * b_pre))) (PreH14 : (delta2 = (a_pre * c_pre))) (PreH15 : (delta0 = (delta1 + ((4 - d) * delta2)))) ,
  ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre)))

noncomputable def Always_positive_return_wit_5 : Prop :=
  (
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
)

noncomputable def Always_positive_return_wit_5_split_goal_1 : Prop :=
  forall (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : (a_pre = (0 : Int))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((0 : Int) = (Always_pos (a_pre) (b_pre) (c_pre)))


structure VC_Correct : Type where
  proof_of_Always_positive_simple_safety_wit_1 : Always_positive_simple_safety_wit_1
  proof_of_Always_positive_simple_safety_wit_2 : Always_positive_simple_safety_wit_2
  proof_of_Always_positive_simple_safety_wit_3 : Always_positive_simple_safety_wit_3
  proof_of_Always_positive_simple_safety_wit_4 : Always_positive_simple_safety_wit_4
  proof_of_Always_positive_simple_safety_wit_5 : Always_positive_simple_safety_wit_5
  proof_of_Always_positive_simple_safety_wit_6 : Always_positive_simple_safety_wit_6
  proof_of_Always_positive_simple_safety_wit_7 : Always_positive_simple_safety_wit_7
  proof_of_Always_positive_simple_safety_wit_8 : Always_positive_simple_safety_wit_8
  proof_of_Always_positive_simple_safety_wit_9 : Always_positive_simple_safety_wit_9
  proof_of_Always_positive_simple_safety_wit_10 : Always_positive_simple_safety_wit_10
  proof_of_Always_positive_safety_wit_1 : Always_positive_safety_wit_1
  proof_of_Always_positive_safety_wit_2 : Always_positive_safety_wit_2
  proof_of_Always_positive_safety_wit_3 : Always_positive_safety_wit_3
  proof_of_Always_positive_safety_wit_4 : Always_positive_safety_wit_4
  proof_of_Always_positive_safety_wit_5 : Always_positive_safety_wit_5
  proof_of_Always_positive_safety_wit_6 : Always_positive_safety_wit_6
  proof_of_Always_positive_safety_wit_7 : Always_positive_safety_wit_7
  proof_of_Always_positive_safety_wit_8 : Always_positive_safety_wit_8
  proof_of_Always_positive_safety_wit_9 : Always_positive_safety_wit_9
  proof_of_Always_positive_safety_wit_10 : Always_positive_safety_wit_10
  proof_of_Always_positive_safety_wit_11 : Always_positive_safety_wit_11
  proof_of_Always_positive_safety_wit_12 : Always_positive_safety_wit_12
  proof_of_Always_positive_safety_wit_13 : Always_positive_safety_wit_13
  proof_of_Always_positive_safety_wit_14 : Always_positive_safety_wit_14
  proof_of_Always_positive_safety_wit_15 : Always_positive_safety_wit_15
  proof_of_Always_positive_safety_wit_16 : Always_positive_safety_wit_16
  proof_of_Always_positive_safety_wit_17 : Always_positive_safety_wit_17
  proof_of_Always_positive_safety_wit_18 : Always_positive_safety_wit_18
  proof_of_Always_positive_safety_wit_19 : Always_positive_safety_wit_19
  proof_of_Always_positive_safety_wit_20 : Always_positive_safety_wit_20
  proof_of_Always_positive_safety_wit_21 : Always_positive_safety_wit_21
  proof_of_Always_positive_safety_wit_22 : Always_positive_safety_wit_22
  proof_of_Always_positive_safety_wit_23 : Always_positive_safety_wit_23
  proof_of_Always_positive_entail_wit_1 : Always_positive_entail_wit_1
  proof_of_Always_positive_simple_return_wit_1 : Always_positive_simple_return_wit_1
  proof_of_Always_positive_simple_return_wit_2 : Always_positive_simple_return_wit_2
  proof_of_Always_positive_simple_return_wit_3 : Always_positive_simple_return_wit_3
  proof_of_Always_positive_simple_return_wit_4 : Always_positive_simple_return_wit_4
  proof_of_Always_positive_entail_wit_2 : Always_positive_entail_wit_2
  proof_of_Always_positive_return_wit_1 : Always_positive_return_wit_1
  proof_of_Always_positive_return_wit_2 : Always_positive_return_wit_2
  proof_of_Always_positive_return_wit_3 : Always_positive_return_wit_3
  proof_of_Always_positive_return_wit_4 : Always_positive_return_wit_4
  proof_of_Always_positive_return_wit_5 : Always_positive_return_wit_5

end SimpleC.EE.QCP_demos_LLM.generated.Always_pos_goal
