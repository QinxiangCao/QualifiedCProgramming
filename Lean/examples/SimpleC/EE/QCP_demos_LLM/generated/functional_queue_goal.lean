import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.sll_lib
import SimpleC.EE.QCP_demos_LLM.functional_queue_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.functional_queue_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance functional_queue_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def push_return_wit_1 : Prop :=
  forall (x_pre : Int) (p_pre : Int) (l : (List Int)) (p_pre_v_2 : Int) (retval_data : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (retval_data = (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (p_pre_v_2))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((p_pre) # Ptr |-> (retval))
  ** (sll p_pre_v_2 l)
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (sll p_pre_v (x_pre :: l))

noncomputable def push_partial_solve_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (p_pre_v : Int) ,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (sll p_pre_v l)
|--
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (sll p_pre_v l)

noncomputable def pop_return_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (x : Int) (y : Int) ,
  (sll y l)
  ** ((p_pre) # Ptr |-> (y))
|--
  EX p_pre_v : Int,
  “ (x = x) ”
  &&  ((p_pre) # Ptr |-> (p_pre_v))
  ** (sll p_pre_v l)

noncomputable def pop_partial_solve_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (x : Int) (p_pre_v : Int) ,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (sll p_pre_v (x :: l))
|--
  EX y : Int,
  ((&((p_pre_v # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll y l)
  ** ((&((p_pre_v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def pop_partial_solve_wit_2 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (x : Int) (p_pre_v : Int) (y : Int) ,
  ((&((p_pre_v # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll y l)
  ** ((&((p_pre_v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((p_pre) # Ptr |-> (y))
|--
  ((&((p_pre_v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((p_pre_v # "list")  ->ₛ "data")) # Int |-> (x))
  ** (sll y l)
  ** ((p_pre) # Ptr |-> (y))

noncomputable def enqueue_entail_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) ,
  (store_queue q_pre l)
|--
  EX ql2 : Int, EX ql1 : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
  ** (sll ql2 l2)
) \/
(
forall (q_pre : Int) (l : (List Int)) ,
  (store_queue q_pre l)
|--
  EX ql2 : Int, EX ql1 : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
  ** (sll ql2 l2)
)

noncomputable def enqueue_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (ql1 : Int) (l1 : (List Int)) (l2 : (List Int)) (p_callee_v : Int) (PreH1 : (l = (l1 ++ (l2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (p_callee_v))
  ** (sll p_callee_v (x_pre :: l2))
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** (sll ql1 l1)
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
) \/
(
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (ql1 : Int) (l1 : (List Int)) (l2 : (List Int)) (p_callee_v : Int) (y : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (l = (l1 ++ (l2).reverse))) ,
  (sll y l2)
  ** ((&((p_callee_v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((p_callee_v # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (p_callee_v))
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** (sll ql1 l1)
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
)

noncomputable def enqueue_return_wit_1_split_goal_spatial : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (ql1 : Int) (l1 : (List Int)) (l2 : (List Int)) (p_callee_v : Int) (y : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (l = (l1 ++ (l2).reverse))) ,
  (sll y l2)
  ** ((&((p_callee_v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((p_callee_v # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (p_callee_v))
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** (sll ql1 l1)
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))

noncomputable def enqueue_partial_solve_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (ql1 : Int) (ql2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = (l1 ++ (l2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
  ** (sll ql2 l2)
|--
  “ (l = (l1 ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql2 l2)
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** (sll ql1 l1)

noncomputable def dequeue_safety_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (ql1 : Int) (ql2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((x :: l) = (l1 ++ (l2).reverse))) ,
  ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
  ** (sll ql2 l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def dequeue_safety_wit_2 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (ql1 : Int) (ql2 : Int) (l1 : (List Int)) (l2 : (List Int)) (retval : Int) (PreH1 : (ql1 = (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2).reverse))) ,
  (sll retval (l2).reverse)
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (retval))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def dequeue_entail_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) ,
  (store_queue q_pre (x :: l))
|--
  EX ql2 : Int, EX ql1 : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ ((x :: l) = (l1 ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
  ** (sll ql2 l2)
) \/
(
forall (q_pre : Int) (l : (List Int)) (x : Int) ,
  (store_queue q_pre (x :: l))
|--
  EX ql2 : Int, EX ql1 : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ ((x :: l) = (l1 ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
  ** (sll ql2 l2)
)

noncomputable def dequeue_entail_wit_2 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) (ql1_2 : Int) (l1 : (List Int)) (l2 : (List Int)) (retval : Int) (PreH1 : (ql1_2 = (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2).reverse))) ,
  (sll retval (l2).reverse)
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (retval))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> ((0 : Int)))
  ** (sll ql1_2 l1)
|--
  EX ql1 : Int, EX rev_l2 : (List Int),
  “ ((x :: l) = rev_l2) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> ((0 : Int)))
  ** (sll ql1 rev_l2)
) \/
(
forall (l : (List Int)) (x : Int) (ql1_2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (ql1_2 = (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2).reverse))) ,
  (sll ql1_2 l1)
|--
  “ ((l2).reverse = (x :: l)) ”
  &&  emp
)

noncomputable def dequeue_entail_wit_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (x : Int) (ql1_2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (ql1_2 = (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2).reverse))) ,
  (sll ql1_2 l1)
|--
  “ ((l2).reverse = (x :: l)) ”

noncomputable def dequeue_entail_wit_2_split_goal_spatial : Prop :=
  forall (l : (List Int)) (x : Int) (ql1_2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (ql1_2 = (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2).reverse))) ,
  (sll ql1_2 l1)
|--
  TT && emp 

noncomputable def dequeue_entail_wit_3 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) (ql1_2 : Int) (ql2_2 : Int) (l1 : (List Int)) (l2_2 : (List Int)) (PreH1 : (ql1_2 ≠ (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2_2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1_2))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2_2))
  ** (sll ql1_2 l1)
  ** (sll ql2_2 l2_2)
|--
  EX ql2 : Int, EX l1_tail : (List Int), EX l2 : (List Int), EX ql1 : Int,
  “ (ql1 ≠ (0 : Int)) ” &&
  “ ((x :: l) = ((x :: l1_tail) ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 (x :: l1_tail))
  ** (sll ql2 l2)
) \/
(
forall (l : (List Int)) (x : Int) (ql1_2 : Int) (l1 : (List Int)) (l2_2 : (List Int)) (PreH1 : (ql1_2 ≠ (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2_2).reverse))) ,
  TT && emp 
|--
  EX l1_tail : (List Int),
  “ (l1 = (x :: l1_tail)) ” &&
  “ ((x :: l) = ((x :: l1_tail) ++ (l2_2).reverse)) ”
  &&  emp
)

noncomputable def dequeue_entail_wit_4_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) (rev_l2 : (List Int)) (ql1_2 : Int) (PreH1 : ((x :: l) = rev_l2)) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1_2))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> ((0 : Int)))
  ** (sll ql1_2 rev_l2)
|--
  EX ql2 : Int, EX ql1 : Int, EX l1_tail : (List Int), EX l2 : (List Int),
  “ ((x :: l) = ((x :: l1_tail) ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 (x :: l1_tail))
  ** (sll ql2 l2)
) \/
(
forall (l : (List Int)) (x : Int) (rev_l2 : (List Int)) (PreH1 : ((x :: l) = rev_l2)) ,
  TT && emp 
|--
  EX l1_tail : (List Int),
  “ ((x :: l) = (x :: l1_tail)) ” &&
  “ ((x :: l) = ((x :: l1_tail) ++ ((@List.nil Int)).reverse)) ”
  &&  emp
)

noncomputable def dequeue_entail_wit_4_2 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (ql1_2 : Int) (ql2_2 : Int) (l1_tail_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (ql1_2 ≠ (0 : Int))) (PreH2 : ((x :: l) = ((x :: l1_tail_2) ++ (l2_2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1_2))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2_2))
  ** (sll ql1_2 (x :: l1_tail_2))
  ** (sll ql2_2 l2_2)
|--
  EX ql2 : Int, EX ql1 : Int, EX l1_tail : (List Int), EX l2 : (List Int),
  “ ((x :: l) = ((x :: l1_tail) ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 (x :: l1_tail))
  ** (sll ql2 l2)

noncomputable def dequeue_return_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) (ql2 : Int) (l1_tail : (List Int)) (l2 : (List Int)) (p_callee_v : Int) (retval : Int) (PreH1 : (retval = x)) (PreH2 : ((x :: l) = ((x :: l1_tail) ++ (l2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (p_callee_v))
  ** (sll p_callee_v l1_tail)
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql2 l2)
|--
  “ (retval = x) ”
  &&  (store_queue q_pre l)
) \/
(
forall (q_pre : Int) (l : (List Int)) (x : Int) (ql2 : Int) (l1_tail : (List Int)) (l2 : (List Int)) (p_callee_v : Int) (retval : Int) (PreH1 : (retval = x)) (PreH2 : ((x :: l) = ((x :: l1_tail) ++ (l2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (p_callee_v))
  ** (sll p_callee_v l1_tail)
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql2 l2)
|--
  (store_queue q_pre l)
)

noncomputable def dequeue_return_wit_1_split_goal_spatial : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (ql2 : Int) (l1_tail : (List Int)) (l2 : (List Int)) (p_callee_v : Int) (retval : Int) (PreH1 : (retval = x)) (PreH2 : ((x :: l) = ((x :: l1_tail) ++ (l2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (p_callee_v))
  ** (sll p_callee_v l1_tail)
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql2 l2)
|--
  (store_queue q_pre l)

noncomputable def dequeue_partial_solve_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (ql1 : Int) (ql2 : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (ql1 = (0 : Int))) (PreH2 : ((x :: l) = (l1 ++ (l2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)
  ** (sll ql2 l2)
|--
  “ (ql1 = (0 : Int)) ” &&
  “ ((x :: l) = (l1 ++ (l2).reverse)) ”
  &&  (sll ql2 l2)
  ** ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 l1)

noncomputable def dequeue_partial_solve_wit_2 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (ql1 : Int) (ql2 : Int) (l1_tail : (List Int)) (l2 : (List Int)) (PreH1 : ((x :: l) = ((x :: l1_tail) ++ (l2).reverse))) ,
  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql1 (x :: l1_tail))
  ** (sll ql2 l2)
|--
  “ ((x :: l) = ((x :: l1_tail) ++ (l2).reverse)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "l1")) # Ptr |-> (ql1))
  ** (sll ql1 (x :: l1_tail))
  ** ((&((q_pre # "queue")  ->ₛ "l2")) # Ptr |-> (ql2))
  ** (sll ql2 l2)


structure VC_Correct : Type where
  proof_of_push_return_wit_1 : push_return_wit_1
  proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1
  proof_of_pop_return_wit_1 : pop_return_wit_1
  proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1
  proof_of_pop_partial_solve_wit_2 : pop_partial_solve_wit_2
  proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1
  proof_of_dequeue_safety_wit_1 : dequeue_safety_wit_1
  proof_of_dequeue_safety_wit_2 : dequeue_safety_wit_2
  proof_of_dequeue_entail_wit_4_2 : dequeue_entail_wit_4_2
  proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1
  proof_of_dequeue_partial_solve_wit_2 : dequeue_partial_solve_wit_2
  proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1
  proof_of_enqueue_return_wit_1 : enqueue_return_wit_1
  proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1
  proof_of_dequeue_entail_wit_2 : dequeue_entail_wit_2
  proof_of_dequeue_entail_wit_3 : dequeue_entail_wit_3
  proof_of_dequeue_entail_wit_4_1 : dequeue_entail_wit_4_1
  proof_of_dequeue_return_wit_1 : dequeue_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.functional_queue_goal
