From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import SimpleC.EE.QCP_demos_LLM.functional_queue_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import functional_queue_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import functional_queue_strategy_proof.

(*----- Function push -----*)

Definition push_return_wit_1 :=
forall (l: (@list Z)) (p_pre: Z) (x_pre: Z) (p_v_2: Z) (retval_data: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (retval_data = 0)),
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> p_v_2)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((p_pre) # Ptr  |-> retval)
  **  (sll p_v_2 l )
|--
  EX (p_v: Z),
  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_pre) (l)) )
.

Definition push_partial_solve_wit_1 :=
forall (l: (@list Z)) (p_pre: Z) (p_v: Z),
  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l )
|--
  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l )
.

(*----- Function pop -----*)

Definition pop_return_wit_1 :=
forall (l: (@list Z)) (x: Z) (p_pre: Z) (y: Z),
  (sll y l )
  **  ((p_pre) # Ptr  |-> y)
|--
  EX (p_v: Z),
  “ (x = x) ”
  &&  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l )
.

Definition pop_partial_solve_wit_1 :=
forall (l: (@list Z)) (x: Z) (p_pre: Z) (p_v: Z),
  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v (cons (x) (l)) )
|--
  EX (y: Z),
  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l )
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((p_pre) # Ptr  |-> p_v)
.

Definition pop_partial_solve_wit_2 :=
forall (l: (@list Z)) (x: Z) (p_pre: Z) (p_v: Z) (y: Z),
  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l )
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((p_pre) # Ptr  |-> y)
|--
  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l )
  **  ((p_pre) # Ptr  |-> y)
.

(*----- Function enqueue -----*)

Definition enqueue_entail_wit_1 :=
(
forall (l: (@list Z)) (q_pre: Z),
  (store_queue q_pre l )
|--
  EX (ql2: Z) (ql1: Z) (l1: (@list Z)) (l2: (@list Z)),
  “ (l = (app (l1) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
  **  (sll ql2 l2 )
) \/
(
forall (l: (@list Z)) (q_pre: Z),
  (store_queue q_pre l )
|--
  EX (ql2: Z) (ql1: Z) (l1: (@list Z)) (l2: (@list Z)),
  “ (l = (app (l1) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
  **  (sll ql2 l2 )
).

Definition enqueue_return_wit_1 :=
(
forall (l: (@list Z)) (q_pre: Z) (x_pre: Z) (ql1: Z) (l1: (@list Z)) (l2: (@list Z)) (p_v: Z) (PreH1 : (l = (app (l1) ((rev (l2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_pre) (l2)) )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  (sll ql1 l1 )
|--
  (store_queue q_pre (app (l) ((cons (x_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (q_pre: Z) (x_pre: Z) (ql1: Z) (l1: (@list Z)) (l2: (@list Z)) (p_v: Z) (y: Z) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (l = (app (l1) ((rev (l2)))))),
  (sll y l2 )
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> p_v)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  (sll ql1 l1 )
|--
  (store_queue q_pre (app (l) ((cons (x_pre) ((@nil Z))))) )
).

Definition enqueue_return_wit_1_split_goal_spatial :=
forall (l: (@list Z)) (q_pre: Z) (x_pre: Z) (ql1: Z) (l1: (@list Z)) (l2: (@list Z)) (p_v: Z) (y: Z) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (l = (app (l1) ((rev (l2)))))),
  (sll y l2 )
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> p_v)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  (sll ql1 l1 )
|--
  (store_queue q_pre (app (l) ((cons (x_pre) ((@nil Z))))) )
.

Definition enqueue_partial_solve_wit_1 :=
forall (l: (@list Z)) (q_pre: Z) (ql1: Z) (ql2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) ((rev (l2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
  **  (sll ql2 l2 )
|--
  “ (l = (app (l1) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql2 l2 )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  (sll ql1 l1 )
.

(*----- Function dequeue -----*)

Definition dequeue_safety_wit_1 :=
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql1: Z) (ql2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((cons (x) (l)) = (app (l1) ((rev (l2)))))),
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
  **  (sll ql2 l2 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dequeue_safety_wit_2 :=
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql1: Z) (ql2: Z) (l1: (@list Z)) (l2: (@list Z)) (retval: Z) (PreH1 : (ql1 = 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2)))))),
  (sll retval (rev (l2)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dequeue_entail_wit_1 :=
(
forall (l: (@list Z)) (x: Z) (q_pre: Z),
  (store_queue q_pre (cons (x) (l)) )
|--
  EX (ql2: Z) (ql1: Z) (l1: (@list Z)) (l2: (@list Z)),
  “ ((cons (x) (l)) = (app (l1) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
  **  (sll ql2 l2 )
) \/
(
forall (l: (@list Z)) (x: Z) (q_pre: Z),
  (store_queue q_pre (cons (x) (l)) )
|--
  EX (ql2: Z) (ql1: Z) (l1: (@list Z)) (l2: (@list Z)),
  “ ((cons (x) (l)) = (app (l1) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
  **  (sll ql2 l2 )
).

Definition dequeue_entail_wit_2 :=
(
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql1_2: Z) (l1: (@list Z)) (l2: (@list Z)) (retval: Z) (PreH1 : (ql1_2 = 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2)))))),
  (sll retval (rev (l2)) )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
  **  (sll ql1_2 l1 )
|--
  EX (ql1: Z) (rev_l2: (@list Z)),
  “ ((cons (x) (l)) = rev_l2) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
  **  (sll ql1 rev_l2 )
) \/
(
forall (l: (@list Z)) (x: Z) (ql1_2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (ql1_2 = 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2)))))),
  (sll ql1_2 l1 )
|--
  “ ((rev (l2)) = (cons (x) (l))) ”
  &&  emp
).

Definition dequeue_entail_wit_2_split_goal_1 :=
forall (l: (@list Z)) (x: Z) (ql1_2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (ql1_2 = 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2)))))),
  (sll ql1_2 l1 )
|--
  “ ((rev (l2)) = (cons (x) (l))) ”
.

Definition dequeue_entail_wit_2_split_goal_spatial :=
forall (l: (@list Z)) (x: Z) (ql1_2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (ql1_2 = 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2)))))),
  (sll ql1_2 l1 )
|--
  TT && emp 
.

Definition dequeue_entail_wit_3 :=
(
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql1_2: Z) (ql2_2: Z) (l1: (@list Z)) (l2_2: (@list Z)) (PreH1 : (ql1_2 <> 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2_2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1_2)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2_2)
  **  (sll ql1_2 l1 )
  **  (sll ql2_2 l2_2 )
|--
  EX (ql2: Z) (l1_tail: (@list Z)) (l2: (@list Z)) (ql1: Z),
  “ (ql1 <> 0) ”
  &&  “ ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 (cons (x) (l1_tail)) )
  **  (sll ql2 l2 )
) \/
(
forall (l: (@list Z)) (x: Z) (ql1_2: Z) (l1: (@list Z)) (l2_2: (@list Z)) (PreH1 : (ql1_2 <> 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2_2)))))),
  TT && emp 
|--
  EX (l1_tail: (@list Z)),
  “ (l1 = (cons (x) (l1_tail))) ”
  &&  “ ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2_2))))) ”
  &&  emp
).

Definition dequeue_entail_wit_4_1 :=
(
forall (l: (@list Z)) (x: Z) (q_pre: Z) (rev_l2: (@list Z)) (ql1_2: Z) (PreH1 : ((cons (x) (l)) = rev_l2)),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1_2)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
  **  (sll ql1_2 rev_l2 )
|--
  EX (ql2: Z) (ql1: Z) (l1_tail: (@list Z)) (l2: (@list Z)),
  “ ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 (cons (x) (l1_tail)) )
  **  (sll ql2 l2 )
) \/
(
forall (l: (@list Z)) (x: Z) (rev_l2: (@list Z)) (PreH1 : ((cons (x) (l)) = rev_l2)),
  TT && emp 
|--
  EX (l1_tail: (@list Z)),
  “ ((cons (x) (l)) = (cons (x) (l1_tail))) ”
  &&  “ ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev ((@nil Z)))))) ”
  &&  emp
).

Definition dequeue_entail_wit_4_2 :=
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql1_2: Z) (ql2_2: Z) (l1_tail_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (ql1_2 <> 0)) (PreH2 : ((cons (x) (l)) = (app ((cons (x) (l1_tail_2))) ((rev (l2_2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1_2)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2_2)
  **  (sll ql1_2 (cons (x) (l1_tail_2)) )
  **  (sll ql2_2 l2_2 )
|--
  EX (ql2: Z) (ql1: Z) (l1_tail: (@list Z)) (l2: (@list Z)),
  “ ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 (cons (x) (l1_tail)) )
  **  (sll ql2 l2 )
.

Definition dequeue_return_wit_1 :=
(
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql2: Z) (l1_tail: (@list Z)) (l2: (@list Z)) (p_v: Z) (retval: Z) (PreH1 : (retval = x)) (PreH2 : ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> p_v)
  **  (sll p_v l1_tail )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql2 l2 )
|--
  “ (retval = x) ”
  &&  (store_queue q_pre l )
) \/
(
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql2: Z) (l1_tail: (@list Z)) (l2: (@list Z)) (p_v: Z) (retval: Z) (PreH1 : (retval = x)) (PreH2 : ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> p_v)
  **  (sll p_v l1_tail )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql2 l2 )
|--
  (store_queue q_pre l )
).

Definition dequeue_return_wit_1_split_goal_spatial :=
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql2: Z) (l1_tail: (@list Z)) (l2: (@list Z)) (p_v: Z) (retval: Z) (PreH1 : (retval = x)) (PreH2 : ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> p_v)
  **  (sll p_v l1_tail )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql2 l2 )
|--
  (store_queue q_pre l )
.

Definition dequeue_partial_solve_wit_1 :=
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql1: Z) (ql2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (ql1 = 0)) (PreH2 : ((cons (x) (l)) = (app (l1) ((rev (l2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
  **  (sll ql2 l2 )
|--
  “ (ql1 = 0) ”
  &&  “ ((cons (x) (l)) = (app (l1) ((rev (l2))))) ”
  &&  (sll ql2 l2 )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 l1 )
.

Definition dequeue_partial_solve_wit_2 :=
forall (l: (@list Z)) (x: Z) (q_pre: Z) (ql1: Z) (ql2: Z) (l1_tail: (@list Z)) (l2: (@list Z)) (PreH1 : ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2)))))),
  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql1 (cons (x) (l1_tail)) )
  **  (sll ql2 l2 )
|--
  “ ((cons (x) (l)) = (app ((cons (x) (l1_tail))) ((rev (l2))))) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> ql1)
  **  (sll ql1 (cons (x) (l1_tail)) )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> ql2)
  **  (sll ql2 l2 )
.

Module Type VC_Correct.

Include sll_Strategy_Correct.
Include functional_queue_Strategy_Correct.

Axiom proof_of_push_return_wit_1 : push_return_wit_1.
Axiom proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1.
Axiom proof_of_pop_return_wit_1 : pop_return_wit_1.
Axiom proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1.
Axiom proof_of_pop_partial_solve_wit_2 : pop_partial_solve_wit_2.
Axiom proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Axiom proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Axiom proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1.
Axiom proof_of_dequeue_safety_wit_1 : dequeue_safety_wit_1.
Axiom proof_of_dequeue_safety_wit_2 : dequeue_safety_wit_2.
Axiom proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1.
Axiom proof_of_dequeue_entail_wit_2 : dequeue_entail_wit_2.
Axiom proof_of_dequeue_entail_wit_3 : dequeue_entail_wit_3.
Axiom proof_of_dequeue_entail_wit_4_1 : dequeue_entail_wit_4_1.
Axiom proof_of_dequeue_entail_wit_4_2 : dequeue_entail_wit_4_2.
Axiom proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Axiom proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1.
Axiom proof_of_dequeue_partial_solve_wit_2 : dequeue_partial_solve_wit_2.

End VC_Correct.
