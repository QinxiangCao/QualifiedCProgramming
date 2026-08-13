import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.sll_lib
import SimpleC.EE.QCP_demos_LLM.sll_queue_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_queue_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_queue_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def enqueue_entail_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) ,
  (store_queue q_pre l)
|--
  EX v : Int, EX u : Int, EX qhead : Int, EX qtail : Int,
  “ (qtail ≠ (0 : Int)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qhead qtail l)
) \/
(
forall (q_pre : Int) (l : (List Int)) ,
  (store_queue q_pre l)
|--
  EX v : Int, EX u : Int, EX qhead : Int, EX qtail : Int,
  “ (qtail ≠ (0 : Int)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qhead qtail l)
)

noncomputable def enqueue_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval_data : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (retval_data = (0 : Int))) (PreH4 : (qtail ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (retval_data))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg qhead qtail l)
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
) \/
(
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval_data : Int) (retval_next : Int) (retval : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (retval_data <= INT_MAX)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval_data >= INT_MIN)) (PreH5 : (retval ≠ (0 : Int))) (PreH6 : (retval_next = (0 : Int))) (PreH7 : (retval_data = (0 : Int))) (PreH8 : (qtail ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (retval_data))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg qhead qtail l)
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
)

noncomputable def enqueue_return_wit_1_split_goal_spatial : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval_data : Int) (retval_next : Int) (retval : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (retval_data <= INT_MAX)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval_data >= INT_MIN)) (PreH5 : (retval ≠ (0 : Int))) (PreH6 : (retval_next = (0 : Int))) (PreH7 : (retval_data = (0 : Int))) (PreH8 : (qtail ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (retval_data))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg qhead qtail l)
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))

noncomputable def enqueue_partial_solve_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (u : Int) (v : Int) (PreH1 : (qtail ≠ (0 : Int))) ,
  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qhead qtail l)
|--
  “ (qtail ≠ (0 : Int)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qhead qtail l)

noncomputable def dequeue_entail_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) ,
  (store_queue q_pre (x :: l))
|--
  EX v : Int, EX u : Int, EX qheadnext : Int, EX qtail : Int, EX qhead : Int,
  “ (qhead ≠ (0 : Int)) ” &&
  “ (qtail ≠ (0 : Int)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qheadnext qtail l)
) \/
(
forall (q_pre : Int) (l : (List Int)) (x : Int) ,
  (store_queue q_pre (x :: l))
|--
  EX v : Int, EX u : Int, EX qheadnext : Int, EX qtail : Int, EX qhead : Int,
  “ (qhead ≠ (0 : Int)) ” &&
  “ (qtail ≠ (0 : Int)) ”
  &&  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qheadnext qtail l)
)

noncomputable def dequeue_return_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (u : Int) (v : Int) (qheadnext : Int) (PreH1 : (qhead ≠ (0 : Int))) (PreH2 : (qtail ≠ (0 : Int))) ,
  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qheadnext qtail l)
|--
  “ (x = x) ”
  &&  (store_queue q_pre l)
) \/
(
forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (u : Int) (v : Int) (qheadnext : Int) (PreH1 : (u <= INT_MAX)) (PreH2 : (u >= INT_MIN)) (PreH3 : (qhead ≠ (0 : Int))) (PreH4 : (qtail ≠ (0 : Int))) ,
  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qheadnext qtail l)
|--
  (store_queue q_pre l)
)

noncomputable def dequeue_return_wit_1_split_goal_spatial : Prop :=
  forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (u : Int) (v : Int) (qheadnext : Int) (PreH1 : (u <= INT_MAX)) (PreH2 : (u >= INT_MIN)) (PreH3 : (qhead ≠ (0 : Int))) (PreH4 : (qtail ≠ (0 : Int))) ,
  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qheadnext qtail l)
|--
  (store_queue q_pre l)

noncomputable def dequeue_partial_solve_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (u : Int) (v : Int) (qheadnext : Int) (PreH1 : (qhead ≠ (0 : Int))) (PreH2 : (qtail ≠ (0 : Int))) ,
  ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qheadnext qtail l)
|--
  “ (qhead ≠ (0 : Int)) ” &&
  “ (qtail ≠ (0 : Int)) ”
  &&  ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (u))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (v))
  ** (sllseg qheadnext qtail l)

noncomputable def init_empty_queue_return_wit_1 : Prop :=
  (
forall (retval_tail : Int) (retval_head : Int) (retval : Int) (retval_data : Int) (retval_next : Int) (retval_2 : Int) (PreH1 : (retval_2 ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (retval_data = (0 : Int))) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : (retval_head = (0 : Int))) (PreH6 : (retval_tail = (0 : Int))) ,
  ((&((retval_2 # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval_2 # "list")  ->ₛ "data")) # Int |-> (retval_data))
  ** ((&((retval # "queue")  ->ₛ "head")) # Ptr |-> (retval_2))
  ** ((&((retval # "queue")  ->ₛ "tail")) # Ptr |-> (retval_2))
|--
  (store_queue retval (@List.nil Int))
) \/
(
forall (retval_tail : Int) (retval_head : Int) (retval : Int) (retval_data : Int) (retval_next : Int) (retval_2 : Int) (PreH1 : (retval_data <= INT_MAX)) (PreH2 : (retval_data >= INT_MIN)) (PreH3 : (retval_2 ≠ (0 : Int))) (PreH4 : (retval_next = (0 : Int))) (PreH5 : (retval_data = (0 : Int))) (PreH6 : (retval ≠ (0 : Int))) (PreH7 : (retval_head = (0 : Int))) (PreH8 : (retval_tail = (0 : Int))) ,
  ((&((retval_2 # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval_2 # "list")  ->ₛ "data")) # Int |-> (retval_data))
  ** ((&((retval # "queue")  ->ₛ "head")) # Ptr |-> (retval_2))
  ** ((&((retval # "queue")  ->ₛ "tail")) # Ptr |-> (retval_2))
|--
  (store_queue retval (@List.nil Int))
)

noncomputable def init_empty_queue_return_wit_1_split_goal_spatial : Prop :=
  forall (retval_tail : Int) (retval_head : Int) (retval : Int) (retval_data : Int) (retval_next : Int) (retval_2 : Int) (PreH1 : (retval_data <= INT_MAX)) (PreH2 : (retval_data >= INT_MIN)) (PreH3 : (retval_2 ≠ (0 : Int))) (PreH4 : (retval_next = (0 : Int))) (PreH5 : (retval_data = (0 : Int))) (PreH6 : (retval ≠ (0 : Int))) (PreH7 : (retval_head = (0 : Int))) (PreH8 : (retval_tail = (0 : Int))) ,
  ((&((retval_2 # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval_2 # "list")  ->ₛ "data")) # Int |-> (retval_data))
  ** ((&((retval # "queue")  ->ₛ "head")) # Ptr |-> (retval_2))
  ** ((&((retval # "queue")  ->ₛ "tail")) # Ptr |-> (retval_2))
|--
  (store_queue retval (@List.nil Int))

noncomputable def init_empty_queue_partial_solve_wit_1 : Prop :=
    TT && emp 
|--
  TT && emp 

noncomputable def init_empty_queue_partial_solve_wit_2 : Prop :=
  forall (retval_tail : Int) (retval_head : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_head = (0 : Int))) (PreH3 : (retval_tail = (0 : Int))) ,
  ((&((retval # "queue")  ->ₛ "head")) # Ptr |-> (retval_head))
  ** ((&((retval # "queue")  ->ₛ "tail")) # Ptr |-> (retval_tail))
|--
  “ (retval ≠ (0 : Int)) ” &&
  “ (retval_head = (0 : Int)) ” &&
  “ (retval_tail = (0 : Int)) ”
  &&  ((&((retval # "queue")  ->ₛ "head")) # Ptr |-> (retval_head))
  ** ((&((retval # "queue")  ->ₛ "tail")) # Ptr |-> (retval_tail))


structure VC_Correct : Type where
  proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1
  proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1
  proof_of_init_empty_queue_partial_solve_wit_1 : init_empty_queue_partial_solve_wit_1
  proof_of_init_empty_queue_partial_solve_wit_2 : init_empty_queue_partial_solve_wit_2
  proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1
  proof_of_enqueue_return_wit_1 : enqueue_return_wit_1
  proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1
  proof_of_dequeue_return_wit_1 : dequeue_return_wit_1
  proof_of_init_empty_queue_return_wit_1 : init_empty_queue_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.sll_queue_goal
