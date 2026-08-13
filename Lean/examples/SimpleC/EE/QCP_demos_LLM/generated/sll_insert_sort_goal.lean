import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.sll_lib
import SimpleC.EE.QCP_demos_LLM.sll_insert_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_insert_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_insert_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def insertion_safety_wit_1 : Prop :=
  forall (node_pre : Int) (p_pre : Int) (a : Int) (l : (List Int)) (p2_v : Int) (p2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (node_pre ≠ (0 : Int))) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (strict_upperbound a l1)) ,
  ((( &( "node" ) )) # Ptr |-> (node_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((( &( "p2" ) )) # Ptr |-> (p2))
  ** (sllbseg ( &( "res" ) ) p2 l1)
  ** ((p2) # Ptr |-> (p2_v))
  ** (sll p2_v l2)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insertion_entail_wit_1 : Prop :=
  (
forall (node_pre : Int) (p_pre : Int) (a : Int) (l : (List Int)) (PreH1 : (node_pre ≠ (0 : Int))) ,
  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sll p_pre l)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (strict_upperbound a l1) ”
  &&  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) ( &( "res" ) ) l1)
  ** (sll p_pre l2)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
) \/
(
forall (node_pre : Int) (a : Int) (l : (List Int)) (PreH1 : (node_pre ≠ (0 : Int))) ,
  TT && emp 
|--
  EX l1 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ l)) ” &&
  “ (strict_upperbound a l1) ”
  &&  (sllbseg ( &( "res" ) ) ( &( "res" ) ) l1)
)

noncomputable def insertion_entail_wit_2 : Prop :=
  (
forall (node_pre : Int) (a : Int) (l : (List Int)) (p2_v_2 : Int) (p2 : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (x : Int) (l0 : (List Int)) (y : Int) (PreH1 : (x < a)) (PreH2 : (l2_2 = (x :: l0))) (PreH3 : (p2_v_2 ≠ (0 : Int))) (PreH4 : (node_pre ≠ (0 : Int))) (PreH5 : (l = (l1_2 ++ l2_2))) (PreH6 : (strict_upperbound a l1_2)) ,
  ((&((p2_v_2 # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll y l0)
  ** ((&((p2_v_2 # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1_2)
  ** ((p2) # Ptr |-> (p2_v_2))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
|--
  EX p2_v : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (strict_upperbound a l1) ”
  &&  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) &((p2_v_2 # "list")  ->ₛ "next") l1)
  ** ((&((p2_v_2 # "list")  ->ₛ "next")) # Ptr |-> (p2_v))
  ** (sll p2_v l2)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
) \/
(
forall (node_pre : Int) (a : Int) (l : (List Int)) (p2_v_2 : Int) (p2 : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (x : Int) (l0 : (List Int)) (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (x < a)) (PreH4 : (l2_2 = (x :: l0))) (PreH5 : (p2_v_2 ≠ (0 : Int))) (PreH6 : (node_pre ≠ (0 : Int))) (PreH7 : (l = (l1_2 ++ l2_2))) (PreH8 : (strict_upperbound a l1_2)) ,
  ((&((p2_v_2 # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sllbseg ( &( "res" ) ) p2 l1_2)
  ** ((p2) # Ptr |-> (p2_v_2))
|--
  EX l1 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ l0)) ” &&
  “ (strict_upperbound a l1) ”
  &&  (sllbseg ( &( "res" ) ) &((p2_v_2 # "list")  ->ₛ "next") l1)
)

noncomputable def insertion_entail_wit_3_1 : Prop :=
  forall (node_pre : Int) (a : Int) (l : (List Int)) (p2_v : Int) (p2 : Int) (l1_3 : (List Int)) (l2 : (List Int)) (PreH1 : (p2_v = (0 : Int))) (PreH2 : (node_pre ≠ (0 : Int))) (PreH3 : (l = (l1_3 ++ l2))) (PreH4 : (strict_upperbound a l1_3)) ,
  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1_3)
  ** ((p2) # Ptr |-> (p2_v))
  ** (sll p2_v l2)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
|--
  (EX l1 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ (@List.nil Int))) ” &&
  “ (strict_upperbound a l1) ”
  &&  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1)
  ** ((p2) # Ptr |-> ((0 : Int)))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_))
  ||
  (EX unext : Int, EX l1_2 : (List Int), EX l0 : (List Int), EX x : Int, EX u : Int,
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (x >= a) ” &&
  “ (l = (l1_2 ++ (x :: l0))) ” &&
  “ (strict_upperbound a l1_2) ”
  &&  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1_2)
  ** ((p2) # Ptr |-> (u))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l0)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_))

noncomputable def insertion_entail_wit_3_2 : Prop :=
  forall (node_pre : Int) (a : Int) (l : (List Int)) (p2_v : Int) (p2 : Int) (l1_3 : (List Int)) (l2 : (List Int)) (x_2 : Int) (l0_2 : (List Int)) (y : Int) (PreH1 : (x_2 >= a)) (PreH2 : (l2 = (x_2 :: l0_2))) (PreH3 : (p2_v ≠ (0 : Int))) (PreH4 : (node_pre ≠ (0 : Int))) (PreH5 : (l = (l1_3 ++ l2))) (PreH6 : (strict_upperbound a l1_3)) ,
  ((&((p2_v # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (sll y l0_2)
  ** ((&((p2_v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1_3)
  ** ((p2) # Ptr |-> (p2_v))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
|--
  (EX l1 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ (@List.nil Int))) ” &&
  “ (strict_upperbound a l1) ”
  &&  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1)
  ** ((p2) # Ptr |-> ((0 : Int)))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_))
  ||
  (EX unext : Int, EX l1_2 : (List Int), EX l0 : (List Int), EX x : Int, EX u : Int,
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (x >= a) ” &&
  “ (l = (l1_2 ++ (x :: l0))) ” &&
  “ (strict_upperbound a l1_2) ”
  &&  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1_2)
  ** ((p2) # Ptr |-> (u))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l0)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_))

noncomputable def insertion_entail_wit_4_1 : Prop :=
  forall (node_pre : Int) (a : Int) (l : (List Int)) (l1_3 : (List Int)) (p2 : Int) (PreH1 : (node_pre ≠ (0 : Int))) (PreH2 : (l = (l1_3 ++ (@List.nil Int)))) (PreH3 : (strict_upperbound a l1_3)) ,
  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1_3)
  ** ((p2) # Ptr |-> (node_pre))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
|--
  (EX resv : Int, EX l1 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ (@List.nil Int))) ” &&
  “ (strict_upperbound a l1) ”
  &&  ((( &( "res" ) )) # Ptr |-> (resv))
  ** (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int))))
  ||
  (EX unext : Int, EX resv_2 : Int, EX l1_2 : (List Int), EX l0 : (List Int), EX x : Int, EX u : Int,
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (x >= a) ” &&
  “ (l = (l1_2 ++ (x :: l0))) ” &&
  “ (strict_upperbound a l1_2) ”
  &&  ((( &( "res" ) )) # Ptr |-> (resv_2))
  ** (sllseg resv_2 node_pre l1_2)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l0))

noncomputable def insertion_entail_wit_4_2 : Prop :=
  forall (node_pre : Int) (a : Int) (l : (List Int)) (l1_3 : (List Int)) (x_2 : Int) (l0_2 : (List Int)) (u_2 : Int) (unext_2 : Int) (p2 : Int) (PreH1 : (node_pre ≠ (0 : Int))) (PreH2 : (u_2 ≠ (0 : Int))) (PreH3 : (x_2 >= a)) (PreH4 : (l = (l1_3 ++ (x_2 :: l0_2)))) (PreH5 : (strict_upperbound a l1_3)) ,
  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1_3)
  ** ((p2) # Ptr |-> (node_pre))
  ** ((&((u_2 # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((u_2 # "list")  ->ₛ "next")) # Ptr |-> (unext_2))
  ** (sll unext_2 l0_2)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> (u_2))
|--
  (EX resv : Int, EX l1 : (List Int),
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ (@List.nil Int))) ” &&
  “ (strict_upperbound a l1) ”
  &&  ((( &( "res" ) )) # Ptr |-> (resv))
  ** (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int))))
  ||
  (EX unext : Int, EX resv_2 : Int, EX l1_2 : (List Int), EX l0 : (List Int), EX x : Int, EX u : Int,
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (x >= a) ” &&
  “ (l = (l1_2 ++ (x :: l0))) ” &&
  “ (strict_upperbound a l1_2) ”
  &&  ((( &( "res" ) )) # Ptr |-> (resv_2))
  ** (sllseg resv_2 node_pre l1_2)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l0))

noncomputable def insertion_return_wit_1 : Prop :=
  (
forall (node_pre : Int) (a : Int) (l : (List Int)) (resv : Int) (l1 : (List Int)) (PreH1 : (node_pre ≠ (0 : Int))) (PreH2 : (l = (l1 ++ (@List.nil Int)))) (PreH3 : (strict_upperbound a l1)) ,
  (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
|--
  EX l0 : (List Int),
  “ (l0 = (insert (a) (l))) ”
  &&  (sll resv l0)
) \/
(
forall (node_pre : Int) (a : Int) (l : (List Int)) (resv : Int) (l1 : (List Int)) (PreH1 : (a <= INT_MAX)) (PreH2 : (a >= INT_MIN)) (PreH3 : (node_pre ≠ (0 : Int))) (PreH4 : (l = (l1 ++ (@List.nil Int)))) (PreH5 : (strict_upperbound a l1)) ,
  (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
|--
  (sll resv (insert (a) (l)))
)

noncomputable def insertion_return_wit_1_split_goal_spatial : Prop :=
  forall (node_pre : Int) (a : Int) (l : (List Int)) (resv : Int) (l1 : (List Int)) (PreH1 : (a <= INT_MAX)) (PreH2 : (a >= INT_MIN)) (PreH3 : (node_pre ≠ (0 : Int))) (PreH4 : (l = (l1 ++ (@List.nil Int)))) (PreH5 : (strict_upperbound a l1)) ,
  (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
|--
  (sll resv (insert (a) (l)))

noncomputable def insertion_return_wit_2 : Prop :=
  (
forall (node_pre : Int) (a : Int) (l : (List Int)) (resv : Int) (l1 : (List Int)) (x : Int) (l0_2 : (List Int)) (u : Int) (unext : Int) (PreH1 : (node_pre ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) (PreH3 : (x >= a)) (PreH4 : (l = (l1 ++ (x :: l0_2)))) (PreH5 : (strict_upperbound a l1)) ,
  (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l0_2)
|--
  EX l0 : (List Int),
  “ (l0 = (insert (a) (l))) ”
  &&  (sll resv l0)
) \/
(
forall (node_pre : Int) (a : Int) (l : (List Int)) (resv : Int) (l1 : (List Int)) (x : Int) (l0_2 : (List Int)) (u : Int) (unext : Int) (PreH1 : (x <= INT_MAX)) (PreH2 : (a <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (a >= INT_MIN)) (PreH5 : (node_pre ≠ (0 : Int))) (PreH6 : (u ≠ (0 : Int))) (PreH7 : (x >= a)) (PreH8 : (l = (l1 ++ (x :: l0_2)))) (PreH9 : (strict_upperbound a l1)) ,
  (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l0_2)
|--
  (sll resv (insert (a) (l)))
)

noncomputable def insertion_return_wit_2_split_goal_spatial : Prop :=
  forall (node_pre : Int) (a : Int) (l : (List Int)) (resv : Int) (l1 : (List Int)) (x : Int) (l0_2 : (List Int)) (u : Int) (unext : Int) (PreH1 : (x <= INT_MAX)) (PreH2 : (a <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (a >= INT_MIN)) (PreH5 : (node_pre ≠ (0 : Int))) (PreH6 : (u ≠ (0 : Int))) (PreH7 : (x >= a)) (PreH8 : (l = (l1 ++ (x :: l0_2)))) (PreH9 : (strict_upperbound a l1)) ,
  (sllseg resv node_pre l1)
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l0_2)
|--
  (sll resv (insert (a) (l)))

noncomputable def insertion_partial_solve_wit_1 : Prop :=
  forall (node_pre : Int) (a : Int) (l : (List Int)) (p2_v : Int) (p2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (p2_v ≠ (0 : Int))) (PreH2 : (node_pre ≠ (0 : Int))) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (strict_upperbound a l1)) ,
  ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1)
  ** ((p2) # Ptr |-> (p2_v))
  ** (sll p2_v l2)
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)
|--
  EX y : Int, EX l0 : (List Int), EX x : Int,
  “ (l2 = (x :: l0)) ” &&
  “ (p2_v ≠ (0 : Int)) ” &&
  “ (node_pre ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (strict_upperbound a l1) ”
  &&  ((&((p2_v # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll y l0)
  ** ((&((p2_v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((node_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** (sllbseg ( &( "res" ) ) p2 l1)
  ** ((p2) # Ptr |-> (p2_v))
  ** ((&((node_pre # "list")  ->ₛ "next")) # Ptr |->_)

noncomputable def insertion_sort_safety_wit_1 : Prop :=
  forall (x_pre : Int) (l : (List Int)) ,
  ((( &( "res" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** (sll x_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insertion_sort_safety_wit_2 : Prop :=
  forall (x_pre : Int) (l : (List Int)) (p : Int) (res : Int) (l0 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = (l1 ++ l2))) (PreH2 : (Permutation l1 l0)) (PreH3 : (increasing l0)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "q" ) )) # Ptr |->_)
  ** ((( &( "res" ) )) # Ptr |-> (res))
  ** (sll res l0)
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** (sll p l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insertion_sort_entail_wit_1 : Prop :=
  (
forall (x_pre : Int) (l : (List Int)) ,
  (sll x_pre l)
|--
  EX l0 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  (sll (0 : Int) l0)
  ** (sll x_pre l2)
) \/
(
forall (l : (List Int)) ,
  TT && emp 
|--
  EX l1 : (List Int),
  “ (l = (l1 ++ l)) ” &&
  “ (Permutation l1 (@List.nil Int)) ” &&
  “ (increasing (@List.nil Int)) ”
  &&  emp
)

noncomputable def insertion_sort_entail_wit_2 : Prop :=
  (
forall (l : (List Int)) (p : Int) (l0_2 : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (x : Int) (l0_3 : (List Int)) (y : Int) (l0_4 : (List Int)) (retval : Int) (PreH1 : (l0_4 = (insert (x) (l0_2)))) (PreH2 : (l2_2 = (x :: l0_3))) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (Permutation l1_2 l0_2)) (PreH6 : (increasing l0_2)) ,
  (sll retval l0_4)
  ** (sll y l0_3)
  ** ((( &( "q" ) )) # Ptr |-> (y))
|--
  EX l0 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  ((( &( "q" ) )) # Ptr |->_)
  ** (sll retval l0)
  ** (sll y l2)
) \/
(
forall (l : (List Int)) (p : Int) (l0_2 : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (x : Int) (l0_3 : (List Int)) (l0_4 : (List Int)) (PreH1 : (l0_4 = (insert (x) (l0_2)))) (PreH2 : (l2_2 = (x :: l0_3))) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (Permutation l1_2 l0_2)) (PreH6 : (increasing l0_2)) ,
  TT && emp 
|--
  EX l1 : (List Int),
  “ ((l1_2 ++ l2_2) = (l1 ++ l0_3)) ” &&
  “ (Permutation l1 (insert (x) (l0_2))) ” &&
  “ (increasing (insert (x) (l0_2))) ”
  &&  emp
)

noncomputable def insertion_sort_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (p : Int) (res : Int) (l0_2 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (p = (0 : Int))) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (Permutation l1 l0_2)) (PreH4 : (increasing l0_2)) ,
  (sll res l0_2)
  ** (sll p l2)
|--
  EX l0 : (List Int),
  “ (Permutation l l0) ” &&
  “ (increasing l0) ”
  &&  (sll res l0)
) \/
(
forall (l : (List Int)) (p : Int) (l0_2 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (p = (0 : Int))) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (Permutation l1 l0_2)) (PreH4 : (increasing l0_2)) ,
  (sll p l2)
|--
  “ (Permutation l l0_2) ”
  &&  emp
)

noncomputable def insertion_sort_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (p : Int) (l0_2 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (p = (0 : Int))) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (Permutation l1 l0_2)) (PreH4 : (increasing l0_2)) ,
  (sll p l2)
|--
  “ (Permutation l l0_2) ”

noncomputable def insertion_sort_return_wit_1_split_goal_spatial : Prop :=
  forall (l : (List Int)) (p : Int) (l0_2 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (p = (0 : Int))) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (Permutation l1 l0_2)) (PreH4 : (increasing l0_2)) ,
  (sll p l2)
|--
  TT && emp 

noncomputable def insertion_sort_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (p : Int) (res : Int) (l0 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (p ≠ (0 : Int))) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (Permutation l1 l0)) (PreH4 : (increasing l0)) ,
  (sll res l0)
  ** (sll p l2)
|--
  EX y : Int, EX l0_2 : (List Int), EX x : Int,
  “ (l2 = (x :: l0_2)) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (sll y l0_2)
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll res l0)

noncomputable def insertion_sort_partial_solve_wit_2_pure : Prop :=
  forall (x_pre : Int) (l : (List Int)) (p : Int) (res : Int) (l0 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (x : Int) (l0_2 : (List Int)) (y : Int) (PreH1 : (l2 = (x :: l0_2))) (PreH2 : (p ≠ (0 : Int))) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (Permutation l1 l0)) (PreH5 : (increasing l0)) ,
  ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (sll y l0_2)
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "q" ) )) # Ptr |-> (y))
  ** ((( &( "res" ) )) # Ptr |-> (res))
  ** (sll res l0)
  ** ((( &( "p" ) )) # Ptr |-> (p))
|--
  “ (p ≠ (0 : Int)) ”

noncomputable def insertion_sort_partial_solve_wit_2_aux : Prop :=
  forall (l : (List Int)) (p : Int) (res : Int) (l0 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (x : Int) (l0_2 : (List Int)) (y : Int) (PreH1 : (l2 = (x :: l0_2))) (PreH2 : (p ≠ (0 : Int))) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (Permutation l1 l0)) (PreH5 : (increasing l0)) ,
  ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (sll y l0_2)
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll res l0)
|--
  “ (p ≠ (0 : Int)) ” &&
  “ (l2 = (x :: l0_2)) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll res l0)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |->_)
  ** (sll y l0_2)

noncomputable def insertion_sort_partial_solve_wit_2 : Prop := insertion_sort_partial_solve_wit_2_pure -> insertion_sort_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_insertion_safety_wit_1 : insertion_safety_wit_1
  proof_of_insertion_entail_wit_3_2 : insertion_entail_wit_3_2
  proof_of_insertion_partial_solve_wit_1 : insertion_partial_solve_wit_1
  proof_of_insertion_sort_safety_wit_1 : insertion_sort_safety_wit_1
  proof_of_insertion_sort_safety_wit_2 : insertion_sort_safety_wit_2
  proof_of_insertion_sort_partial_solve_wit_1 : insertion_sort_partial_solve_wit_1
  proof_of_insertion_sort_partial_solve_wit_2_pure : insertion_sort_partial_solve_wit_2_pure
  proof_of_insertion_sort_partial_solve_wit_2 : insertion_sort_partial_solve_wit_2
  proof_of_insertion_entail_wit_1 : insertion_entail_wit_1
  proof_of_insertion_entail_wit_2 : insertion_entail_wit_2
  proof_of_insertion_entail_wit_3_1 : insertion_entail_wit_3_1
  proof_of_insertion_entail_wit_4_1 : insertion_entail_wit_4_1
  proof_of_insertion_entail_wit_4_2 : insertion_entail_wit_4_2
  proof_of_insertion_return_wit_1 : insertion_return_wit_1
  proof_of_insertion_return_wit_2 : insertion_return_wit_2
  proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1
  proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2
  proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.sll_insert_sort_goal
