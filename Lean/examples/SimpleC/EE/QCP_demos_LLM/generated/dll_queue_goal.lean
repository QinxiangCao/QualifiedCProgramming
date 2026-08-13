import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.dll_queue_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.dll_queue_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance dll_queue_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def enqueue_safety_wit_1 : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((( &( "p" ) )) # Ptr |-> (retval))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def enqueue_safety_wit_2 : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval : Int) (PreH1 : (qhead = (0 : Int))) (PreH2 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((( &( "p" ) )) # Ptr |-> (retval))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (retval))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def enqueue_safety_wit_3 : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval : Int) (PreH1 : (qhead = (0 : Int))) (PreH2 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** ((( &( "p" ) )) # Ptr |-> (retval))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (retval))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def enqueue_safety_wit_4 : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (l0 : (List Int)) (qtailv : Int) (qtail : Int) (qhead : Int) (qtailnext : Int) (qtailprev : Int) (p : Int) (PreH1 : (p ≠ (0 : Int))) (PreH2 : (qtail ≠ (0 : Int))) (PreH3 : (qhead ≠ (0 : Int))) (PreH4 : (l = (l0 ++ (qtailv :: (@List.nil Int))))) (PreH5 : (qtailnext = (0 : Int))) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** (dllseg qhead qtail (0 : Int) qtailprev l0)
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (p))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (p))
  ** ((&((qtail # "list")  ->ₛ "prev")) # Ptr |-> (qtailprev))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (qtailv))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (qtail))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def enqueue_entail_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) ,
  (store_queue q_pre l)
|--
  EX qhead : Int, EX qtail : Int,
  (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
) \/
(
forall (q_pre : Int) (l : (List Int)) ,
  (store_queue q_pre l)
|--
  EX qhead : Int, EX qtail : Int,
  (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
)

noncomputable def enqueue_entail_wit_2 : Prop :=
  (
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead_2 : Int) (qtail_2 : Int) (retval : Int) (PreH1 : (qhead_2 ≠ (0 : Int))) (PreH2 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** (dllseg qhead_2 (0 : Int) (0 : Int) qtail_2 l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead_2))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail_2))
|--
  EX qtailprev : Int, EX qtailnext : Int, EX l0 : (List Int), EX qtailv : Int, EX qhead : Int, EX qtail : Int,
  “ (retval ≠ (0 : Int)) ” &&
  “ (qtail ≠ (0 : Int)) ” &&
  “ (qhead ≠ (0 : Int)) ” &&
  “ (l = (l0 ++ (qtailv :: (@List.nil Int)))) ” &&
  “ (qtailnext = (0 : Int)) ”
  &&  (dllseg qhead qtail (0 : Int) qtailprev l0)
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (qtailnext))
  ** ((&((qtail # "list")  ->ₛ "prev")) # Ptr |-> (qtailprev))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (qtailv))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
) \/
(
forall (l : (List Int)) (qhead_2 : Int) (qtail_2 : Int) (retval : Int) (PreH1 : (qhead_2 ≠ (0 : Int))) (PreH2 : (retval ≠ (0 : Int))) ,
  (dllseg qhead_2 (0 : Int) (0 : Int) qtail_2 l)
|--
  EX qtailprev : Int, EX l0 : (List Int), EX qtailv : Int,
  “ (retval ≠ (0 : Int)) ” &&
  “ (qtail_2 ≠ (0 : Int)) ” &&
  “ (qhead_2 ≠ (0 : Int)) ” &&
  “ (l = (l0 ++ (qtailv :: (@List.nil Int)))) ”
  &&  (dllseg qhead_2 qtail_2 (0 : Int) qtailprev l0)
  ** ((&((qtail_2 # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((qtail_2 # "list")  ->ₛ "prev")) # Ptr |-> (qtailprev))
  ** ((&((qtail_2 # "list")  ->ₛ "data")) # Int |-> (qtailv))
)

noncomputable def enqueue_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval : Int) (PreH1 : (qhead = (0 : Int))) (PreH2 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (retval))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
) \/
(
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (qhead = (0 : Int))) (PreH4 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (retval))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
)

noncomputable def enqueue_return_wit_1_split_goal_spatial : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (retval : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (qhead = (0 : Int))) (PreH4 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x_pre))
  ** (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (retval))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (retval))
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))

noncomputable def enqueue_return_wit_2 : Prop :=
  (
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (l0 : (List Int)) (qtailv : Int) (qtail : Int) (qhead : Int) (qtailnext : Int) (qtailprev : Int) (p : Int) (PreH1 : (p ≠ (0 : Int))) (PreH2 : (qtail ≠ (0 : Int))) (PreH3 : (qhead ≠ (0 : Int))) (PreH4 : (l = (l0 ++ (qtailv :: (@List.nil Int))))) (PreH5 : (qtailnext = (0 : Int))) ,
  (dllseg qhead qtail (0 : Int) qtailprev l0)
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (p))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (p))
  ** ((&((qtail # "list")  ->ₛ "prev")) # Ptr |-> (qtailprev))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (qtailv))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (qtail))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x_pre))
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
) \/
(
forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (l0 : (List Int)) (qtailv : Int) (qtail : Int) (qhead : Int) (qtailnext : Int) (qtailprev : Int) (p : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (qtailv <= INT_MAX)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (qtailv >= INT_MIN)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (qtail ≠ (0 : Int))) (PreH7 : (qhead ≠ (0 : Int))) (PreH8 : (l = (l0 ++ (qtailv :: (@List.nil Int))))) (PreH9 : (qtailnext = (0 : Int))) ,
  (dllseg qhead qtail (0 : Int) qtailprev l0)
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (p))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (p))
  ** ((&((qtail # "list")  ->ₛ "prev")) # Ptr |-> (qtailprev))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (qtailv))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (qtail))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x_pre))
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))
)

noncomputable def enqueue_return_wit_2_split_goal_spatial : Prop :=
  forall (x_pre : Int) (q_pre : Int) (l : (List Int)) (l0 : (List Int)) (qtailv : Int) (qtail : Int) (qhead : Int) (qtailnext : Int) (qtailprev : Int) (p : Int) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (qtailv <= INT_MAX)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (qtailv >= INT_MIN)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (qtail ≠ (0 : Int))) (PreH7 : (qhead ≠ (0 : Int))) (PreH8 : (l = (l0 ++ (qtailv :: (@List.nil Int))))) (PreH9 : (qtailnext = (0 : Int))) ,
  (dllseg qhead qtail (0 : Int) qtailprev l0)
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (p))
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((qtail # "list")  ->ₛ "next")) # Ptr |-> (p))
  ** ((&((qtail # "list")  ->ₛ "prev")) # Ptr |-> (qtailprev))
  ** ((&((qtail # "list")  ->ₛ "data")) # Int |-> (qtailv))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (qtail))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x_pre))
|--
  (store_queue q_pre (l ++ (x_pre :: (@List.nil Int))))

noncomputable def enqueue_partial_solve_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) ,
  (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  (dllseg qhead (0 : Int) (0 : Int) qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))

noncomputable def dequeue_safety_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (qheadnext : Int) (PreH1 : (qhead ≠ (0 : Int))) ,
  ((( &( "x0" ) )) # Int |-> (x))
  ** ((( &( "p" ) )) # Ptr |-> (qhead))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def dequeue_safety_wit_2 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (qheadnext : Int) (PreH1 : (qheadnext = (0 : Int))) (PreH2 : (qhead ≠ (0 : Int))) ,
  ((( &( "x0" ) )) # Int |-> (x))
  ** ((( &( "p" ) )) # Ptr |-> (qhead))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def dequeue_safety_wit_3 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (headv : Int) (qheadnext : Int) (l0 : (List Int)) (p : Int) (PreH1 : (qhead ≠ (0 : Int))) (PreH2 : (l = (headv :: l0))) ,
  ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "x0" ) )) # Int |-> (x))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> (p))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (headv))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead qtail l0)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def dequeue_entail_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) ,
  (store_queue q_pre (x :: l))
|--
  EX qtail : Int, EX qheadnext : Int, EX qhead : Int,
  “ (qhead ≠ (0 : Int)) ”
  &&  ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
) \/
(
forall (q_pre : Int) (l : (List Int)) (x : Int) ,
  (store_queue q_pre (x :: l))
|--
  EX qtail : Int, EX qheadnext : Int, EX qhead : Int,
  “ (qhead ≠ (0 : Int)) ”
  &&  ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
)

noncomputable def dequeue_entail_wit_2 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail_2 : Int) (qheadnext_2 : Int) (PreH1 : (qheadnext_2 ≠ (0 : Int))) (PreH2 : (qhead ≠ (0 : Int))) ,
  (dllseg qheadnext_2 (0 : Int) qhead qtail_2 l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext_2))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail_2))
|--
  EX qtail : Int, EX qheadnext : Int, EX headv : Int, EX l0 : (List Int), EX qhead_2 : Int,
  “ (qhead_2 ≠ (0 : Int)) ” &&
  “ (l = (headv :: l0)) ”
  &&  ((&((qhead_2 # "list")  ->ₛ "prev")) # Ptr |-> (qhead))
  ** ((&((qhead_2 # "list")  ->ₛ "data")) # Int |-> (headv))
  ** ((&((qhead_2 # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead_2 qtail l0)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead_2))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
) \/
(
forall (l : (List Int)) (qhead : Int) (qtail_2 : Int) (qheadnext_2 : Int) (PreH1 : (qheadnext_2 ≠ (0 : Int))) (PreH2 : (qhead ≠ (0 : Int))) ,
  (dllseg qheadnext_2 (0 : Int) qhead qtail_2 l)
|--
  EX qheadnext : Int, EX headv : Int, EX l0 : (List Int),
  “ (qheadnext_2 ≠ (0 : Int)) ” &&
  “ (l = (headv :: l0)) ”
  &&  ((&((qheadnext_2 # "list")  ->ₛ "prev")) # Ptr |-> (qhead))
  ** ((&((qheadnext_2 # "list")  ->ₛ "data")) # Int |-> (headv))
  ** ((&((qheadnext_2 # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qheadnext_2 qtail_2 l0)
)

noncomputable def dequeue_return_wit_1 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (qheadnext : Int) (PreH1 : (qheadnext = (0 : Int))) (PreH2 : (qhead ≠ (0 : Int))) ,
  (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> ((0 : Int)))
|--
  “ (x = x) ”
  &&  (store_queue q_pre l)
) \/
(
forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (qheadnext : Int) (PreH1 : (qheadnext = (0 : Int))) (PreH2 : (qhead ≠ (0 : Int))) ,
  (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> ((0 : Int)))
|--
  (store_queue q_pre l)
)

noncomputable def dequeue_return_wit_1_split_goal_spatial : Prop :=
  forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (qheadnext : Int) (PreH1 : (qheadnext = (0 : Int))) (PreH2 : (qhead ≠ (0 : Int))) ,
  (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> ((0 : Int)))
|--
  (store_queue q_pre l)

noncomputable def dequeue_return_wit_2 : Prop :=
  (
forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (headv : Int) (qheadnext : Int) (l0 : (List Int)) (PreH1 : (qhead ≠ (0 : Int))) (PreH2 : (l = (headv :: l0))) ,
  ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (headv))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead qtail l0)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  “ (x = x) ”
  &&  (store_queue q_pre l)
) \/
(
forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (headv : Int) (qheadnext : Int) (l0 : (List Int)) (PreH1 : (headv <= INT_MAX)) (PreH2 : (headv >= INT_MIN)) (PreH3 : (qhead ≠ (0 : Int))) (PreH4 : (l = (headv :: l0))) ,
  ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (headv))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead qtail l0)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  (store_queue q_pre l)
)

noncomputable def dequeue_return_wit_2_split_goal_spatial : Prop :=
  forall (q_pre : Int) (l : (List Int)) (qhead : Int) (qtail : Int) (headv : Int) (qheadnext : Int) (l0 : (List Int)) (PreH1 : (headv <= INT_MAX)) (PreH2 : (headv >= INT_MIN)) (PreH3 : (qhead ≠ (0 : Int))) (PreH4 : (l = (headv :: l0))) ,
  ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (headv))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead qtail l0)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qhead))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  (store_queue q_pre l)

noncomputable def dequeue_partial_solve_wit_1 : Prop :=
  forall (q_pre : Int) (l : (List Int)) (x : Int) (qhead : Int) (qtail : Int) (qheadnext : Int) (PreH1 : (qhead ≠ (0 : Int))) ,
  ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))
|--
  “ (qhead ≠ (0 : Int)) ”
  &&  ((&((qhead # "list")  ->ₛ "next")) # Ptr |-> (qheadnext))
  ** ((&((qhead # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((qhead # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dllseg qheadnext (0 : Int) qhead qtail l)
  ** ((&((q_pre # "queue")  ->ₛ "head")) # Ptr |-> (qheadnext))
  ** ((&((q_pre # "queue")  ->ₛ "tail")) # Ptr |-> (qtail))


structure VC_Correct : Type where
  proof_of_enqueue_safety_wit_1 : enqueue_safety_wit_1
  proof_of_enqueue_safety_wit_2 : enqueue_safety_wit_2
  proof_of_enqueue_safety_wit_3 : enqueue_safety_wit_3
  proof_of_enqueue_safety_wit_4 : enqueue_safety_wit_4
  proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1
  proof_of_dequeue_safety_wit_1 : dequeue_safety_wit_1
  proof_of_dequeue_safety_wit_2 : dequeue_safety_wit_2
  proof_of_dequeue_safety_wit_3 : dequeue_safety_wit_3
  proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1
  proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1
  proof_of_enqueue_entail_wit_2 : enqueue_entail_wit_2
  proof_of_enqueue_return_wit_1 : enqueue_return_wit_1
  proof_of_enqueue_return_wit_2 : enqueue_return_wit_2
  proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1
  proof_of_dequeue_entail_wit_2 : dequeue_entail_wit_2
  proof_of_dequeue_return_wit_1 : dequeue_return_wit_1
  proof_of_dequeue_return_wit_2 : dequeue_return_wit_2

end SimpleC.EE.QCP_demos_LLM.generated.dll_queue_goal
