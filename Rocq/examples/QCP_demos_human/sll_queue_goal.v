Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.sll_lib.
Require Import SimpleC.EE.QCP_demos_human.sll_queue_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_proof.
From SimpleC.EE.QCP_demos_human Require Import sll_queue_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_queue_strategy_proof.

(*----- Function enqueue -----*)

Definition enqueue_return_wit_1 := 
(
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval_data: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (retval_data = 0)) (PreH4 : (q_tail <> 0)) ,
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> retval_data)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (sllseg q_head q_tail l )
|--
  (store_queue q_pre (app (l) ((cons (x_pre) ((@nil Z))))) )
) \/
(
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval_data: Z) (retval_next: Z) (retval: Z) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (retval_data <= INT_MAX)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval_data >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval_next = 0)) (PreH7 : (retval_data = 0)) (PreH8 : (q_tail <> 0)) ,
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> retval_data)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (sllseg q_head q_tail l )
|--
  (store_queue q_pre (app (l) ((cons (x_pre) ((@nil Z))))) )
).

Definition enqueue_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval_data: Z) (retval_next: Z) (retval: Z) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (retval_data <= INT_MAX)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval_data >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval_next = 0)) (PreH7 : (retval_data = 0)) (PreH8 : (q_tail <> 0)) ,
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> retval_data)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (sllseg q_head q_tail l )
|--
  (store_queue q_pre (app (l) ((cons (x_pre) ((@nil Z))))) )
.

Definition enqueue_partial_solve_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) ,
  (store_queue q_pre l )
|--
  (store_queue q_pre l )
.

Definition enqueue_partial_solve_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (q_head: Z) (v: Z) (u: Z) (q_tail: Z) (PreH1 : (q_tail <> 0)) ,
  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (sllseg q_head q_tail l )
|--
  “ (q_tail <> 0) ”
  &&  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (sllseg q_head q_tail l )
.

Definition enqueue_which_implies_wit_1 := 
(
forall (l: (@list Z)) (q: Z) ,
  (store_queue q l )
|--
  EX (q_head: Z)  (v: Z)  (u: Z)  (q_tail: Z) ,
  “ (q_tail <> 0) ”
  &&  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (sllseg q_head q_tail l )
) \/
(
forall (l: (@list Z)) (q: Z) ,
  (store_queue q l )
|--
  EX (q_head: Z)  (v: Z)  (u: Z)  (q_tail: Z) ,
  “ (q_tail <> 0) ”
  &&  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (sllseg q_head q_tail l )
).

(*----- Function dequeue -----*)

Definition dequeue_return_wit_1 := 
(
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next: Z) (v: Z) (u: Z) (q_tail: Z) (PreH1 : (q_tail <> 0)) ,
  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  (sllseg q_head_next q_tail l )
|--
  “ (x = x) ”
  &&  (store_queue q_pre l )
) \/
(
forall (q_pre: Z) (l: (@list Z)) (q_head_next: Z) (v: Z) (u: Z) (q_tail: Z) (PreH1 : (u <= INT_MAX)) (PreH2 : (u >= INT_MIN)) (PreH3 : (q_tail <> 0)) ,
  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  (sllseg q_head_next q_tail l )
|--
  (store_queue q_pre l )
).

Definition dequeue_return_wit_1_split_goal_spatial := 
forall (q_pre: Z) (l: (@list Z)) (q_head_next: Z) (v: Z) (u: Z) (q_tail: Z) (PreH1 : (u <= INT_MAX)) (PreH2 : (u >= INT_MIN)) (PreH3 : (q_tail <> 0)) ,
  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  (sllseg q_head_next q_tail l )
|--
  (store_queue q_pre l )
.

Definition dequeue_partial_solve_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) ,
  (store_queue q_pre (cons (x) (l)) )
|--
  (store_queue q_pre (cons (x) (l)) )
.

Definition dequeue_partial_solve_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next: Z) (q_head: Z) (v: Z) (u: Z) (q_tail: Z) (PreH1 : (q_tail <> 0)) ,
  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (sllseg q_head_next q_tail l )
|--
  “ (q_tail <> 0) ”
  &&  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  (sllseg q_head_next q_tail l )
.

Definition dequeue_which_implies_wit_1 := 
(
forall (l: (@list Z)) (x: Z) (q: Z) ,
  (store_queue q (cons (x) (l)) )
|--
  EX (q_head_next: Z)  (q_head: Z)  (v: Z)  (u: Z)  (q_tail: Z) ,
  “ (q_tail <> 0) ”
  &&  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (sllseg q_head_next q_tail l )
) \/
(
forall (l: (@list Z)) (x: Z) (q: Z) ,
  (store_queue q (cons (x) (l)) )
|--
  EX (q_head_next: Z)  (q_head: Z)  (v: Z)  (u: Z)  (q_tail: Z) ,
  “ (q_tail <> 0) ”
  &&  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> u)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> v)
  **  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (sllseg q_head_next q_tail l )
).

(*----- Function init_empty_queue -----*)

Definition init_empty_queue_return_wit_1 := 
(
forall (retval_tail: Z) (retval_head: Z) (retval: Z) (retval_data: Z) (retval_next: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (retval_data = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval_head = 0)) (PreH6 : (retval_tail = 0)) ,
  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> retval_data)
  **  ((&((retval)  # "queue" ->ₛ "head")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "queue" ->ₛ "tail")) # Ptr  |-> retval_2)
|--
  (store_queue retval (@nil Z) )
) \/
(
forall (retval_tail: Z) (retval_head: Z) (retval: Z) (retval_data: Z) (retval_next: Z) (retval_2: Z) (PreH1 : (retval_data <= INT_MAX)) (PreH2 : (retval_data >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (retval_data = 0)) (PreH6 : (retval <> 0)) (PreH7 : (retval_head = 0)) (PreH8 : (retval_tail = 0)) ,
  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> retval_data)
  **  ((&((retval)  # "queue" ->ₛ "head")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "queue" ->ₛ "tail")) # Ptr  |-> retval_2)
|--
  (store_queue retval (@nil Z) )
).

Definition init_empty_queue_return_wit_1_split_goal_spatial := 
forall (retval_tail: Z) (retval_head: Z) (retval: Z) (retval_data: Z) (retval_next: Z) (retval_2: Z) (PreH1 : (retval_data <= INT_MAX)) (PreH2 : (retval_data >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (retval_data = 0)) (PreH6 : (retval <> 0)) (PreH7 : (retval_head = 0)) (PreH8 : (retval_tail = 0)) ,
  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> retval_data)
  **  ((&((retval)  # "queue" ->ₛ "head")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "queue" ->ₛ "tail")) # Ptr  |-> retval_2)
|--
  (store_queue retval (@nil Z) )
.

Definition init_empty_queue_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition init_empty_queue_partial_solve_wit_2 := 
forall (retval_tail: Z) (retval_head: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_head = 0)) (PreH3 : (retval_tail = 0)) ,
  ((&((retval)  # "queue" ->ₛ "head")) # Ptr  |-> retval_head)
  **  ((&((retval)  # "queue" ->ₛ "tail")) # Ptr  |-> retval_tail)
|--
  “ (retval <> 0) ” 
  &&  “ (retval_head = 0) ” 
  &&  “ (retval_tail = 0) ”
  &&  ((&((retval)  # "queue" ->ₛ "head")) # Ptr  |-> retval_head)
  **  ((&((retval)  # "queue" ->ₛ "tail")) # Ptr  |-> retval_tail)
.

Module Type VC_Correct.

Include sll_Strategy_Correct.
Include sll_queue_Strategy_Correct.

Axiom proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Axiom proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1.
Axiom proof_of_enqueue_partial_solve_wit_2 : enqueue_partial_solve_wit_2.
Axiom proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Axiom proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Axiom proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1.
Axiom proof_of_dequeue_partial_solve_wit_2 : dequeue_partial_solve_wit_2.
Axiom proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Axiom proof_of_init_empty_queue_return_wit_1 : init_empty_queue_return_wit_1.
Axiom proof_of_init_empty_queue_partial_solve_wit_1 : init_empty_queue_partial_solve_wit_1.
Axiom proof_of_init_empty_queue_partial_solve_wit_2 : init_empty_queue_partial_solve_wit_2.

End VC_Correct.
