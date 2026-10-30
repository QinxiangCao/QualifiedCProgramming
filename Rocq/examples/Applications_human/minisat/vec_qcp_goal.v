From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.vec_qcp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_strategy_goal.
From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_strategy_proof.

(*----- Function veci_new -----*)

Definition veci_new_safety_wit_1 :=
forall (v_pre: Z),
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  (Veci.shell v_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition veci_new_safety_wit_2 :=
forall (v_pre: Z),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition veci_new_safety_wit_3 :=
forall (v_pre: Z),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> 0)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition veci_new_return_wit_1 :=
(
forall (v_pre: Z),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> 0)
|--
  (Veci.rep v_pre (@nil Z) )
) \/
(
  TT && emp 
|--
  “ (0 <= (Zlength ((@nil Z)))) ”
  &&  “ ((Zlength ((@nil Z))) <= 0) ”
  &&  “ (vec_buf_ok 0 0 ) ”
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  (IntArray.undef_seg 0 (Zlength ((@nil Z))) 0 )
  **  (IntArray.seg 0 0 (Zlength ((@nil Z))) (@nil Z) )
).

Definition veci_new_return_wit_1_split_goal_1 :=
  (0 <= (Zlength ((@nil Z))))
.

Definition veci_new_return_wit_1_split_goal_2 :=
  ((Zlength ((@nil Z))) <= 0)
.

Definition veci_new_return_wit_1_split_goal_3 :=
  (vec_buf_ok 0 0 )
.

Definition veci_new_return_wit_1_split_goal_4 :=
  (0 = (Zlength ((@nil Z))))
.

Definition veci_new_return_wit_1_split_goal_spatial :=
  TT && emp 
|--
  (IntArray.undef_seg 0 (Zlength ((@nil Z))) 0 )
  **  (IntArray.seg 0 0 (Zlength ((@nil Z))) (@nil Z) )
.

Definition veci_new_partial_solve_wit_1 :=
forall (v_pre: Z),
  (Veci.shell v_pre )
|--
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |->_)
.

(*----- Function veci_delete -----*)

Definition veci_delete_return_wit_1 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
|--
  (Veci.shell v_pre )
.

Definition veci_delete_partial_solve_wit_1 :=
forall (l: (@list Z)) (v_pre: Z),
  (Veci.rep v_pre l )
|--
  EX (p: Z) (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
.

Definition veci_delete_partial_solve_wit_2_pure :=
(
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (0 <= (Zlength (l))) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
) \/
(
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : ((Zlength (l)) >= INT_MIN)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (vec_buf_ok cap p )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
).

Definition veci_delete_partial_solve_wit_2_pure_split_goal_1 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : ((Zlength (l)) >= INT_MIN)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (vec_buf_ok cap p )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
.

Definition veci_delete_partial_solve_wit_2_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
|--
  “ (0 <= (Zlength (l))) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (IntArray.seg p 0 (Zlength (l)) l )
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
.

Definition veci_delete_partial_solve_wit_2 := veci_delete_partial_solve_wit_2_pure -> veci_delete_partial_solve_wit_2_aux.

(*----- Function veci_begin -----*)

Definition veci_begin_return_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
|--
  “ (p = p) ”
  &&  (Veci.rep_ptr v_pre p l )
.

Definition veci_begin_partial_solve_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z),
  (Veci.rep_ptr v_pre p l )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
.

(*----- Function veci_size -----*)

Definition veci_size_return_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ ((Zlength (l)) = (Zlength (l))) ”
  &&  (Veci.rep_ptr v_pre p l )
.

Definition veci_size_partial_solve_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z),
  (Veci.rep_ptr v_pre p l )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
.

(*----- Function veci_resize -----*)

Definition veci_resize_return_wit_1 :=
(
forall (l: (@list Z)) (p: Z) (v_pre: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) = k_pre) ”
  &&  (Veci.rep_ptr v_pre p (sublist (0) (k_pre) (l)) )
) \/
(
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) = k_pre) ”
  &&  “ (0 <= (Zlength ((sublist (0) (k_pre) (l))))) ”
  &&  “ ((Zlength ((sublist (0) (k_pre) (l)))) <= cap) ”
  &&  “ (k_pre = (Zlength ((sublist (0) (k_pre) (l))))) ”
  &&  (IntArray.undef_seg p (Zlength ((sublist (0) (k_pre) (l)))) cap )
  **  (IntArray.seg p 0 (Zlength ((sublist (0) (k_pre) (l)))) (sublist (0) (k_pre) (l)) )
).

Definition veci_resize_return_wit_1_split_goal_1 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) = k_pre) ”
.

Definition veci_resize_return_wit_1_split_goal_2 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
|--
  “ (0 <= (Zlength ((sublist (0) (k_pre) (l))))) ”
.

Definition veci_resize_return_wit_1_split_goal_3 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) <= cap) ”
.

Definition veci_resize_return_wit_1_split_goal_4 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
|--
  “ (k_pre = (Zlength ((sublist (0) (k_pre) (l))))) ”
.

Definition veci_resize_return_wit_1_split_goal_spatial :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
|--
  (IntArray.undef_seg p (Zlength ((sublist (0) (k_pre) (l)))) cap )
  **  (IntArray.seg p 0 (Zlength ((sublist (0) (k_pre) (l)))) (sublist (0) (k_pre) (l)) )
.

Definition veci_resize_partial_solve_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z) (k_pre: Z) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= (Zlength (l)))),
  (Veci.rep_ptr v_pre p l )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
.

(*----- Function vec_next_capacity -----*)

Definition vec_next_capacity_safety_wit_1 :=
forall (cap_pre: Z) (PreH1 : (0 <= cap_pre)) (PreH2 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ (INT_MAX <= INT_MAX) ”
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition vec_next_capacity_safety_wit_2 :=
forall (cap_pre: Z) (PreH1 : (0 = 1)) (PreH2 : (cap_pre = INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ False ”
.

Definition vec_next_capacity_safety_wit_3 :=
forall (cap_pre: Z) (PreH1 : (cap_pre <> INT_MAX)) (PreH2 : (0 <= cap_pre)) (PreH3 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ (1073741823 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1073741823) ”
.

Definition vec_next_capacity_safety_wit_4 :=
forall (cap_pre: Z) (PreH1 : (cap_pre > 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ ((cap_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cap_pre + 1 )) ”
.

Definition vec_next_capacity_safety_wit_5 :=
forall (cap_pre: Z) (PreH1 : (cap_pre > 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vec_next_capacity_safety_wit_6 :=
forall (cap_pre: Z) (PreH1 : (cap_pre <= 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ (((cap_pre * 2 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((cap_pre * 2 ) + 1 )) ”
.

Definition vec_next_capacity_safety_wit_7 :=
forall (cap_pre: Z) (PreH1 : (cap_pre <= 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ ((cap_pre * 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cap_pre * 2 )) ”
.

Definition vec_next_capacity_safety_wit_8 :=
forall (cap_pre: Z) (PreH1 : (cap_pre <= 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition vec_next_capacity_safety_wit_9 :=
forall (cap_pre: Z) (PreH1 : (cap_pre <= 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  ((( &( "cap" ) )) # Int  |-> cap_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vec_next_capacity_return_wit_1 :=
forall (cap_pre: Z) (PreH1 : (cap_pre <= 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  TT && emp 
|--
  “ (cap_pre < ((cap_pre * 2 ) + 1 )) ”
  &&  “ (((cap_pre * 2 ) + 1 ) <= INT_MAX) ”
  &&  “ (((cap_pre * 2 ) + 1 ) = ((cap_pre * 2 ) + 1 )) ”
  &&  “ (cap_pre <= 1073741823) ”
  &&  emp
.

Definition vec_next_capacity_return_wit_2 :=
forall (cap_pre: Z) (PreH1 : (cap_pre > 1073741823)) (PreH2 : (cap_pre <> INT_MAX)) (PreH3 : (0 <= cap_pre)) (PreH4 : (cap_pre <= INT_MAX)),
  TT && emp 
|--
  “ (cap_pre < (cap_pre + 1 )) ”
  &&  “ ((cap_pre + 1 ) <= INT_MAX) ”
  &&  “ ((cap_pre + 1 ) = (cap_pre + 1 )) ”
  &&  “ (cap_pre > 1073741823) ”
  &&  emp
.

Definition vec_next_capacity_partial_solve_wit_1 :=
forall (cap_pre: Z) (PreH1 : (cap_pre = INT_MAX)) (PreH2 : (0 <= cap_pre)) (PreH3 : (cap_pre <= INT_MAX)),
  TT && emp 
|--
  “ (cap_pre = INT_MAX) ”
  &&  “ (0 <= cap_pre) ”
  &&  “ (cap_pre <= INT_MAX) ”
  &&  emp
.

(*----- Function veci_push -----*)

Definition veci_push_safety_wit_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition veci_push_safety_wit_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition veci_push_safety_wit_3 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition veci_push_safety_wit_4 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition veci_push_safety_wit_5 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  (IntArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition veci_push_entail_wit_1_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (cap < actual)) (PreH3 : (actual <= retval)) (PreH4 : (actual = retval)) (PreH5 : (cap < retval)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval = ((cap * 2 ) + 1 ))) (PreH8 : (cap <= 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 cap l )
  **  (IntArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  (“ ((Zlength (l)) < actual) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  (IntArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
  ||
  (EX (actual_2: Z) (retval_3: Z),
  “ ((Zlength (l)) < actual_2) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (cap < actual_2) ”
  &&  “ (actual_2 <= retval) ”
  &&  “ (actual_2 = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_2)
  **  (IntArray.seg retval_3 0 cap l )
  **  (IntArray.undef_seg retval_3 cap actual_2 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_3)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
.

Definition veci_push_entail_wit_1_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (cap < actual_2)) (PreH3 : (actual_2 <= retval)) (PreH4 : (actual_2 = (cap + 1 ))) (PreH5 : (cap < retval)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval = ((cap * 2 ) + 1 ))) (PreH8 : (cap <= 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_3 0 cap l )
  **  (IntArray.undef_seg retval_3 cap actual_2 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_3)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_2)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  (EX (actual: Z) (retval_2: Z),
  “ ((Zlength (l)) < actual) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  (IntArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
  ||
  (“ ((Zlength (l)) < actual_2) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (cap < actual_2) ”
  &&  “ (actual_2 <= retval) ”
  &&  “ (actual_2 = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_2)
  **  (IntArray.seg retval_3 0 cap l )
  **  (IntArray.undef_seg retval_3 cap actual_2 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_3)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
.

Definition veci_push_entail_wit_1_3 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval_4: Z) (actual_3: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (cap < actual_3)) (PreH3 : (actual_3 <= retval_4)) (PreH4 : (actual_3 = retval_4)) (PreH5 : (cap < retval_4)) (PreH6 : (retval_4 <= INT_MAX)) (PreH7 : (retval_4 = (cap + 1 ))) (PreH8 : (cap > 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_5 0 cap l )
  **  (IntArray.undef_seg retval_5 cap actual_3 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_5)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_3)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  (“ ((Zlength (l)) < actual_3) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ (cap < actual_3) ”
  &&  “ (actual_3 <= retval_4) ”
  &&  “ (actual_3 = retval_4) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_3)
  **  (IntArray.seg retval_5 0 cap l )
  **  (IntArray.undef_seg retval_5 cap actual_3 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_5)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
  ||
  (EX (actual_4: Z) (retval_6: Z),
  “ ((Zlength (l)) < actual_4) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_6 <> 0) ”
  &&  “ (cap < actual_4) ”
  &&  “ (actual_4 <= retval_4) ”
  &&  “ (actual_4 = (cap + 1 )) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_4)
  **  (IntArray.seg retval_6 0 cap l )
  **  (IntArray.undef_seg retval_6 cap actual_4 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_6)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
.

Definition veci_push_entail_wit_1_4 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval_4: Z) (actual_4: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (cap < actual_4)) (PreH3 : (actual_4 <= retval_4)) (PreH4 : (actual_4 = (cap + 1 ))) (PreH5 : (cap < retval_4)) (PreH6 : (retval_4 <= INT_MAX)) (PreH7 : (retval_4 = (cap + 1 ))) (PreH8 : (cap > 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_6 0 cap l )
  **  (IntArray.undef_seg retval_6 cap actual_4 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_6)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_4)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  (EX (actual_3: Z) (retval_5: Z),
  “ ((Zlength (l)) < actual_3) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ (cap < actual_3) ”
  &&  “ (actual_3 <= retval_4) ”
  &&  “ (actual_3 = retval_4) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_3)
  **  (IntArray.seg retval_5 0 cap l )
  **  (IntArray.undef_seg retval_5 cap actual_3 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_5)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
  ||
  (“ ((Zlength (l)) < actual_4) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_6 <> 0) ”
  &&  “ (cap < actual_4) ”
  &&  “ (actual_4 <= retval_4) ”
  &&  “ (actual_4 = (cap + 1 )) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual_4)
  **  (IntArray.seg retval_6 0 cap l )
  **  (IntArray.undef_seg retval_6 cap actual_4 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_6)
  **  ((( &( "e" ) )) # Int  |-> e_pre))
.

Definition veci_push_entail_wit_1_5 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <> cap)) (PreH2 : (vec_buf_ok cap p )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ ((Zlength (l)) < cap) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ ((Zlength (l)) <> cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (l)) >= INT_MIN)) (PreH6 : ((Zlength (l)) <> cap)) (PreH7 : (vec_buf_ok cap p )) (PreH8 : (cap <= INT_MAX)) (PreH9 : ((Zlength (l)) <= cap)) (PreH10 : (0 <= (Zlength (l)))),
  TT && emp 
|--
  “ ((Zlength (l)) < cap) ”
  &&  emp
).

Definition veci_push_entail_wit_1_5_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (l)) >= INT_MIN)) (PreH6 : ((Zlength (l)) <> cap)) (PreH7 : (vec_buf_ok cap p )) (PreH8 : (cap <= INT_MAX)) (PreH9 : ((Zlength (l)) <= cap)) (PreH10 : (0 <= (Zlength (l)))),
  ((Zlength (l)) < cap)
.

Definition veci_push_return_wit_1 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Veci.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= ((cap * 2 ) + 1 )) ”
  &&  “ (vec_buf_ok ((cap * 2 ) + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition veci_push_return_wit_1_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_1_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= ((cap * 2 ) + 1 )) ”
.

Definition veci_push_return_wit_1_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ (vec_buf_ok ((cap * 2 ) + 1 ) retval_2 ) ”
.

Definition veci_push_return_wit_1_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_1_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition veci_push_return_wit_2 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Veci.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
  &&  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition veci_push_return_wit_2_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_2_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
.

Definition veci_push_return_wit_2_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
.

Definition veci_push_return_wit_2_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_2_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition veci_push_return_wit_3 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Veci.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
  &&  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition veci_push_return_wit_3_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_3_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
.

Definition veci_push_return_wit_3_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
.

Definition veci_push_return_wit_3_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_3_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition veci_push_return_wit_4 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Veci.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
  &&  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition veci_push_return_wit_4_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_4_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
.

Definition veci_push_return_wit_4_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
.

Definition veci_push_return_wit_4_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_4_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  (IntArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  (IntArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (IntArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition veci_push_return_wit_5 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  (IntArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
|--
  (Veci.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  (IntArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= cap) ”
  &&  “ (((Zlength (l)) + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (IntArray.undef_seg p (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) cap )
  **  (IntArray.seg p 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition veci_push_return_wit_5_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  (IntArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_5_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  (IntArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= cap) ”
.

Definition veci_push_return_wit_5_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  (IntArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ (((Zlength (l)) + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition veci_push_return_wit_5_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  (IntArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  (IntArray.undef_seg p (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) cap )
  **  (IntArray.seg p 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition veci_push_partial_solve_wit_1 :=
forall (l: (@list Z)) (v_pre: Z),
  (Veci.rep v_pre l )
|--
  EX (p: Z) (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition veci_push_partial_solve_wit_2_pure :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) = cap)) (PreH2 : (vec_buf_ok cap p )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
.

Definition veci_push_partial_solve_wit_2_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) = cap)) (PreH2 : (vec_buf_ok cap p )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition veci_push_partial_solve_wit_2 := veci_push_partial_solve_wit_2_pure -> veci_push_partial_solve_wit_2_aux.

Definition veci_push_partial_solve_wit_3_pure :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = ((cap * 2 ) + 1 ))) (PreH4 : (cap <= 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
) \/
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (l)) >= INT_MIN)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap < retval)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (retval = ((cap * 2 ) + 1 ))) (PreH10 : (cap <= 1073741823)) (PreH11 : ((Zlength (l)) = cap)) (PreH12 : (vec_buf_ok cap p )) (PreH13 : (cap <= INT_MAX)) (PreH14 : ((Zlength (l)) <= cap)) (PreH15 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
).

Definition veci_push_partial_solve_wit_3_pure_split_goal_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (l)) >= INT_MIN)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap < retval)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (retval = ((cap * 2 ) + 1 ))) (PreH10 : (cap <= 1073741823)) (PreH11 : ((Zlength (l)) = cap)) (PreH12 : (vec_buf_ok cap p )) (PreH13 : (cap <= INT_MAX)) (PreH14 : ((Zlength (l)) <= cap)) (PreH15 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
.

Definition veci_push_partial_solve_wit_3_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = ((cap * 2 ) + 1 ))) (PreH4 : (cap <= 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (IntArray.seg p 0 cap l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition veci_push_partial_solve_wit_3 := veci_push_partial_solve_wit_3_pure -> veci_push_partial_solve_wit_3_aux.

Definition veci_push_partial_solve_wit_4_pure :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = (cap + 1 ))) (PreH4 : (cap > 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
.

Definition veci_push_partial_solve_wit_4_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = (cap + 1 ))) (PreH4 : (cap > 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (IntArray.seg p 0 cap l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition veci_push_partial_solve_wit_4 := veci_push_partial_solve_wit_4_pure -> veci_push_partial_solve_wit_4_aux.

Definition veci_push_partial_solve_wit_5 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  (IntArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition veci_push_partial_solve_wit_6 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = ((cap * 2 ) + 1 ))) (PreH11 : (cap <= 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  (IntArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition veci_push_partial_solve_wit_7 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = retval)) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  (IntArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition veci_push_partial_solve_wit_8 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : (retval_2 <> 0)) (PreH5 : (cap < actual)) (PreH6 : (actual <= retval)) (PreH7 : (actual = (cap + 1 ))) (PreH8 : (cap < retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (retval = (cap + 1 ))) (PreH11 : (cap > 1073741823)) (PreH12 : ((Zlength (l)) = cap)) (PreH13 : (vec_buf_ok cap p )) (PreH14 : (cap <= INT_MAX)) (PreH15 : ((Zlength (l)) <= cap)) (PreH16 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  (IntArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> actual)
  **  (IntArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition veci_push_partial_solve_wit_9 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : (e_pre <= INT_MAX)) (PreH3 : (e_pre >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  (IntArray.undef_seg p (Zlength (l)) cap )
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
|--
  “ ((Zlength (l)) < cap) ”
  &&  “ (e_pre <= INT_MAX) ”
  &&  “ (e_pre >= INT_MIN) ”
  &&  “ ((Zlength (l)) <> cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((p + ((Zlength (l)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg p ((Zlength (l)) + 1 ) cap )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  (IntArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> p)
.

(*----- Function vecp_new -----*)

Definition vecp_new_safety_wit_1 :=
forall (v_pre: Z),
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  (Vecp.shell v_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vecp_new_safety_wit_2 :=
forall (v_pre: Z),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (4 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 4) ”
.

Definition vecp_new_return_wit_1 :=
(
forall (v_pre: Z) (retval: Z) (PreH1 : (retval <> 0)),
  (PtrArray.undef_full retval 4 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
|--
  (Vecp.rep v_pre (@nil Z) )
) \/
(
forall (retval: Z) (PreH1 : (retval <> 0)),
  (PtrArray.undef_full retval 4 )
|--
  “ (0 <= (Zlength ((@nil Z)))) ”
  &&  “ ((Zlength ((@nil Z))) <= 4) ”
  &&  “ (vec_buf_ok 4 retval ) ”
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  (PtrArray.undef_seg retval (Zlength ((@nil Z))) 4 )
  **  (PtrArray.seg retval 0 (Zlength ((@nil Z))) (@nil Z) )
).

Definition vecp_new_return_wit_1_split_goal_1 :=
forall (retval: Z) (PreH1 : (retval <> 0)),
  (PtrArray.undef_full retval 4 )
|--
  “ (0 <= (Zlength ((@nil Z)))) ”
.

Definition vecp_new_return_wit_1_split_goal_2 :=
forall (retval: Z) (PreH1 : (retval <> 0)),
  (PtrArray.undef_full retval 4 )
|--
  “ ((Zlength ((@nil Z))) <= 4) ”
.

Definition vecp_new_return_wit_1_split_goal_3 :=
forall (retval: Z) (PreH1 : (retval <> 0)),
  (PtrArray.undef_full retval 4 )
|--
  “ (vec_buf_ok 4 retval ) ”
.

Definition vecp_new_return_wit_1_split_goal_4 :=
forall (retval: Z) (PreH1 : (retval <> 0)),
  (PtrArray.undef_full retval 4 )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition vecp_new_return_wit_1_split_goal_spatial :=
forall (retval: Z) (PreH1 : (retval <> 0)),
  (PtrArray.undef_full retval 4 )
|--
  (PtrArray.undef_seg retval (Zlength ((@nil Z))) 4 )
  **  (PtrArray.seg retval 0 (Zlength ((@nil Z))) (@nil Z) )
.

Definition vecp_new_partial_solve_wit_1 :=
forall (v_pre: Z),
  (Vecp.shell v_pre )
|--
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |->_)
.

Definition vecp_new_partial_solve_wit_2_pure :=
forall (v_pre: Z),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (4 > 0) ”
.

Definition vecp_new_partial_solve_wit_2_aux :=
forall (v_pre: Z),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
|--
  “ (4 > 0) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
.

Definition vecp_new_partial_solve_wit_2 := vecp_new_partial_solve_wit_2_pure -> vecp_new_partial_solve_wit_2_aux.

(*----- Function vecp_delete -----*)

Definition vecp_delete_return_wit_1 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
|--
  (Vecp.shell v_pre )
.

Definition vecp_delete_partial_solve_wit_1 :=
forall (l: (@list Z)) (v_pre: Z),
  (Vecp.rep v_pre l )
|--
  EX (p: Z) (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
.

Definition vecp_delete_partial_solve_wit_2_pure :=
(
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ (0 <= (Zlength (l))) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
) \/
(
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : ((Zlength (l)) >= INT_MIN)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (vec_buf_ok cap p )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
).

Definition vecp_delete_partial_solve_wit_2_pure_split_goal_1 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : ((Zlength (l)) >= INT_MIN)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (vec_buf_ok cap p )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
.

Definition vecp_delete_partial_solve_wit_2_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
|--
  “ (0 <= (Zlength (l))) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (PtrArray.seg p 0 (Zlength (l)) l )
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
.

Definition vecp_delete_partial_solve_wit_2 := vecp_delete_partial_solve_wit_2_pure -> vecp_delete_partial_solve_wit_2_aux.

(*----- Function vecp_begin -----*)

Definition vecp_begin_return_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
|--
  “ (p = p) ”
  &&  (Vecp.rep_ptr v_pre p l )
.

Definition vecp_begin_partial_solve_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z),
  (Vecp.rep_ptr v_pre p l )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
.

(*----- Function vecp_size -----*)

Definition vecp_size_return_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ ((Zlength (l)) = (Zlength (l))) ”
  &&  (Vecp.rep_ptr v_pre p l )
.

Definition vecp_size_partial_solve_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z),
  (Vecp.rep_ptr v_pre p l )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
.

(*----- Function vecp_resize -----*)

Definition vecp_resize_return_wit_1 :=
(
forall (l: (@list Z)) (p: Z) (v_pre: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> k_pre)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) = k_pre) ”
  &&  (Vecp.rep_ptr v_pre p (sublist (0) (k_pre) (l)) )
) \/
(
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) = k_pre) ”
  &&  “ (0 <= (Zlength ((sublist (0) (k_pre) (l))))) ”
  &&  “ ((Zlength ((sublist (0) (k_pre) (l)))) <= cap) ”
  &&  “ (k_pre = (Zlength ((sublist (0) (k_pre) (l))))) ”
  &&  (PtrArray.undef_seg p (Zlength ((sublist (0) (k_pre) (l)))) cap )
  **  (PtrArray.seg p 0 (Zlength ((sublist (0) (k_pre) (l)))) (sublist (0) (k_pre) (l)) )
).

Definition vecp_resize_return_wit_1_split_goal_1 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) = k_pre) ”
.

Definition vecp_resize_return_wit_1_split_goal_2 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
|--
  “ (0 <= (Zlength ((sublist (0) (k_pre) (l))))) ”
.

Definition vecp_resize_return_wit_1_split_goal_3 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
|--
  “ ((Zlength ((sublist (0) (k_pre) (l)))) <= cap) ”
.

Definition vecp_resize_return_wit_1_split_goal_4 :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
|--
  “ (k_pre = (Zlength ((sublist (0) (k_pre) (l))))) ”
.

Definition vecp_resize_return_wit_1_split_goal_spatial :=
forall (l: (@list Z)) (p: Z) (k_pre: Z) (cap: Z) (PreH1 : (vec_buf_ok cap p )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (l)) <= cap)) (PreH4 : (0 <= (Zlength (l)))) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= (Zlength (l)))),
  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
|--
  (PtrArray.undef_seg p (Zlength ((sublist (0) (k_pre) (l)))) cap )
  **  (PtrArray.seg p 0 (Zlength ((sublist (0) (k_pre) (l)))) (sublist (0) (k_pre) (l)) )
.

Definition vecp_resize_partial_solve_wit_1 :=
forall (l: (@list Z)) (p: Z) (v_pre: Z) (k_pre: Z) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= (Zlength (l)))),
  (Vecp.rep_ptr v_pre p l )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  “ (0 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |->_)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
.

(*----- Function vecp_push -----*)

Definition vecp_push_safety_wit_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition vecp_push_safety_wit_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition vecp_push_safety_wit_3 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition vecp_push_safety_wit_4 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition vecp_push_safety_wit_5 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  (PtrArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (((Zlength (l)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Zlength (l)) + 1 )) ”
.

Definition vecp_push_entail_wit_1_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (cap < actual)) (PreH3 : (actual <= retval)) (PreH4 : (actual = retval)) (PreH5 : (cap < retval)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval = ((cap * 2 ) + 1 ))) (PreH8 : (cap <= 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 cap l )
  **  (PtrArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  (“ ((Zlength (l)) < actual) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  (PtrArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
  ||
  (EX (actual_2: Z) (retval_3: Z),
  “ ((Zlength (l)) < actual_2) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (cap < actual_2) ”
  &&  “ (actual_2 <= retval) ”
  &&  “ (actual_2 = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_2)
  **  (PtrArray.seg retval_3 0 cap l )
  **  (PtrArray.undef_seg retval_3 cap actual_2 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_3)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
.

Definition vecp_push_entail_wit_1_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (cap < actual_2)) (PreH3 : (actual_2 <= retval)) (PreH4 : (actual_2 = (cap + 1 ))) (PreH5 : (cap < retval)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval = ((cap * 2 ) + 1 ))) (PreH8 : (cap <= 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_3 0 cap l )
  **  (PtrArray.undef_seg retval_3 cap actual_2 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_3)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_2)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  (EX (actual: Z) (retval_2: Z),
  “ ((Zlength (l)) < actual) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  (PtrArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
  ||
  (“ ((Zlength (l)) < actual_2) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (cap < actual_2) ”
  &&  “ (actual_2 <= retval) ”
  &&  “ (actual_2 = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_2)
  **  (PtrArray.seg retval_3 0 cap l )
  **  (PtrArray.undef_seg retval_3 cap actual_2 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_3)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
.

Definition vecp_push_entail_wit_1_3 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval_4: Z) (actual_3: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (cap < actual_3)) (PreH3 : (actual_3 <= retval_4)) (PreH4 : (actual_3 = retval_4)) (PreH5 : (cap < retval_4)) (PreH6 : (retval_4 <= INT_MAX)) (PreH7 : (retval_4 = (cap + 1 ))) (PreH8 : (cap > 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_5 0 cap l )
  **  (PtrArray.undef_seg retval_5 cap actual_3 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_5)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_3)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  (“ ((Zlength (l)) < actual_3) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ (cap < actual_3) ”
  &&  “ (actual_3 <= retval_4) ”
  &&  “ (actual_3 = retval_4) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_3)
  **  (PtrArray.seg retval_5 0 cap l )
  **  (PtrArray.undef_seg retval_5 cap actual_3 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_5)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
  ||
  (EX (actual_4: Z) (retval_6: Z),
  “ ((Zlength (l)) < actual_4) ”
  &&  “ (retval_6 <> 0) ”
  &&  “ (cap < actual_4) ”
  &&  “ (actual_4 <= retval_4) ”
  &&  “ (actual_4 = (cap + 1 )) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_4)
  **  (PtrArray.seg retval_6 0 cap l )
  **  (PtrArray.undef_seg retval_6 cap actual_4 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_6)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
.

Definition vecp_push_entail_wit_1_4 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval_4: Z) (actual_4: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (cap < actual_4)) (PreH3 : (actual_4 <= retval_4)) (PreH4 : (actual_4 = (cap + 1 ))) (PreH5 : (cap < retval_4)) (PreH6 : (retval_4 <= INT_MAX)) (PreH7 : (retval_4 = (cap + 1 ))) (PreH8 : (cap > 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_6 0 cap l )
  **  (PtrArray.undef_seg retval_6 cap actual_4 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_6)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_4)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  (EX (actual_3: Z) (retval_5: Z),
  “ ((Zlength (l)) < actual_3) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ (cap < actual_3) ”
  &&  “ (actual_3 <= retval_4) ”
  &&  “ (actual_3 = retval_4) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_3)
  **  (PtrArray.seg retval_5 0 cap l )
  **  (PtrArray.undef_seg retval_5 cap actual_3 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_5)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
  ||
  (“ ((Zlength (l)) < actual_4) ”
  &&  “ (retval_6 <> 0) ”
  &&  “ (cap < actual_4) ”
  &&  “ (actual_4 <= retval_4) ”
  &&  “ (actual_4 = (cap + 1 )) ”
  &&  “ (cap < retval_4) ”
  &&  “ (retval_4 <= INT_MAX) ”
  &&  “ (retval_4 = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual_4)
  **  (PtrArray.seg retval_6 0 cap l )
  **  (PtrArray.undef_seg retval_6 cap actual_4 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_6)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre))
.

Definition vecp_push_entail_wit_1_5 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <> cap)) (PreH2 : (vec_buf_ok cap p )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ ((Zlength (l)) < cap) ”
  &&  “ ((Zlength (l)) <> cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
) \/
(
forall (l: (@list Z)) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : (cap >= INT_MIN)) (PreH3 : ((Zlength (l)) >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  TT && emp 
|--
  “ ((Zlength (l)) < cap) ”
  &&  emp
).

Definition vecp_push_entail_wit_1_5_split_goal_1 :=
forall (l: (@list Z)) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : (cap >= INT_MIN)) (PreH3 : ((Zlength (l)) >= INT_MIN)) (PreH4 : ((Zlength (l)) <> cap)) (PreH5 : (vec_buf_ok cap p )) (PreH6 : (cap <= INT_MAX)) (PreH7 : ((Zlength (l)) <= cap)) (PreH8 : (0 <= (Zlength (l)))),
  ((Zlength (l)) < cap)
.

Definition vecp_push_return_wit_1 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Vecp.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= ((cap * 2 ) + 1 )) ”
  &&  “ (vec_buf_ok ((cap * 2 ) + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition vecp_push_return_wit_1_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_1_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= ((cap * 2 ) + 1 )) ”
.

Definition vecp_push_return_wit_1_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ (vec_buf_ok ((cap * 2 ) + 1 ) retval_2 ) ”
.

Definition vecp_push_return_wit_1_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_1_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
|--
  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition vecp_push_return_wit_2 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Vecp.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
  &&  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition vecp_push_return_wit_2_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_2_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
.

Definition vecp_push_return_wit_2_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
.

Definition vecp_push_return_wit_2_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_2_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition vecp_push_return_wit_3 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Vecp.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
  &&  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition vecp_push_return_wit_3_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_3_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
.

Definition vecp_push_return_wit_3_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
.

Definition vecp_push_return_wit_3_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_3_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition vecp_push_return_wit_4 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg retval_2 (cap + 1 ) actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  (Vecp.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
  &&  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
  &&  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition vecp_push_return_wit_4_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_4_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= (cap + 1 )) ”
.

Definition vecp_push_return_wit_4_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ (vec_buf_ok (cap + 1 ) retval_2 ) ”
.

Definition vecp_push_return_wit_4_split_goal_4 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  “ ((cap + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_4_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  (PtrArray.seg retval_2 0 (cap + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
|--
  (PtrArray.undef_seg retval_2 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) actual )
  **  (PtrArray.seg retval_2 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition vecp_push_return_wit_5 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  (PtrArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (l)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
|--
  (Vecp.rep v_pre (app (l) ((cons (e_pre) ((@nil Z))))) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  (PtrArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= cap) ”
  &&  “ (((Zlength (l)) + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
  &&  (PtrArray.undef_seg p (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) cap )
  **  (PtrArray.seg p 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
).

Definition vecp_push_return_wit_5_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  (PtrArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ (0 <= (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_5_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  (PtrArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ ((Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) <= cap) ”
.

Definition vecp_push_return_wit_5_split_goal_3 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  (PtrArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  “ (((Zlength (l)) + 1 ) = (Zlength ((app (l) ((cons (e_pre) ((@nil Z)))))))) ”
.

Definition vecp_push_return_wit_5_split_goal_spatial :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  (PtrArray.seg p 0 ((Zlength (l)) + 1 ) (app (l) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
|--
  (PtrArray.undef_seg p (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) cap )
  **  (PtrArray.seg p 0 (Zlength ((app (l) ((cons (e_pre) ((@nil Z))))))) (app (l) ((cons (e_pre) ((@nil Z))))) )
.

Definition vecp_push_partial_solve_wit_1 :=
forall (l: (@list Z)) (v_pre: Z),
  (Vecp.rep v_pre l )
|--
  EX (p: Z) (cap: Z),
  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition vecp_push_partial_solve_wit_2_pure :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) = cap)) (PreH2 : (vec_buf_ok cap p )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
.

Definition vecp_push_partial_solve_wit_2_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) = cap)) (PreH2 : (vec_buf_ok cap p )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ (0 <= cap) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition vecp_push_partial_solve_wit_2 := vecp_push_partial_solve_wit_2_pure -> vecp_push_partial_solve_wit_2_aux.

Definition vecp_push_partial_solve_wit_3_pure :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = ((cap * 2 ) + 1 ))) (PreH4 : (cap <= 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
) \/
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : (cap >= INT_MIN)) (PreH3 : ((Zlength (l)) >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cap < retval)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval = ((cap * 2 ) + 1 ))) (PreH8 : (cap <= 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
).

Definition vecp_push_partial_solve_wit_3_pure_split_goal_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : ((Zlength (l)) <= INT_MAX)) (PreH2 : (cap >= INT_MIN)) (PreH3 : ((Zlength (l)) >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cap < retval)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval = ((cap * 2 ) + 1 ))) (PreH8 : (cap <= 1073741823)) (PreH9 : ((Zlength (l)) = cap)) (PreH10 : (vec_buf_ok cap p )) (PreH11 : (cap <= INT_MAX)) (PreH12 : ((Zlength (l)) <= cap)) (PreH13 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ ((cap = 0) -> (p = 0)) ”
.

Definition vecp_push_partial_solve_wit_3_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = ((cap * 2 ) + 1 ))) (PreH4 : (cap <= 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (PtrArray.seg p 0 cap l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition vecp_push_partial_solve_wit_3 := vecp_push_partial_solve_wit_3_pure -> vecp_push_partial_solve_wit_3_aux.

Definition vecp_push_partial_solve_wit_4_pure :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = (cap + 1 ))) (PreH4 : (cap > 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((( &( "new_cap" ) )) # Int  |-> retval)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
.

Definition vecp_push_partial_solve_wit_4_aux :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (PreH1 : (cap < retval)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (retval = (cap + 1 ))) (PreH4 : (cap > 1073741823)) (PreH5 : ((Zlength (l)) = cap)) (PreH6 : (vec_buf_ok cap p )) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zlength (l)) <= cap)) (PreH9 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
|--
  “ (0 <= cap) ”
  &&  “ (cap = cap) ”
  &&  “ (cap < retval) ”
  &&  “ ((cap = 0) -> (p = 0)) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (PtrArray.seg p 0 cap l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
.

Definition vecp_push_partial_solve_wit_4 := vecp_push_partial_solve_wit_4_pure -> vecp_push_partial_solve_wit_4_aux.

Definition vecp_push_partial_solve_wit_5 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  (PtrArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition vecp_push_partial_solve_wit_6 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = ((cap * 2 ) + 1 ))) (PreH9 : (cap <= 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  (PtrArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = ((cap * 2 ) + 1 )) ”
  &&  “ (cap <= 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition vecp_push_partial_solve_wit_7 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = retval)) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  (PtrArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = retval) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition vecp_push_partial_solve_wit_8 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (retval: Z) (actual: Z) (retval_2: Z) (PreH1 : ((Zlength (l)) < actual)) (PreH2 : (retval_2 <> 0)) (PreH3 : (cap < actual)) (PreH4 : (actual <= retval)) (PreH5 : (actual = (cap + 1 ))) (PreH6 : (cap < retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (retval = (cap + 1 ))) (PreH9 : (cap > 1073741823)) (PreH10 : ((Zlength (l)) = cap)) (PreH11 : (vec_buf_ok cap p )) (PreH12 : (cap <= INT_MAX)) (PreH13 : ((Zlength (l)) <= cap)) (PreH14 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  (PtrArray.undef_seg retval_2 cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
|--
  “ ((Zlength (l)) < actual) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (cap < actual) ”
  &&  “ (actual <= retval) ”
  &&  “ (actual = (cap + 1 )) ”
  &&  “ (cap < retval) ”
  &&  “ (retval <= INT_MAX) ”
  &&  “ (retval = (cap + 1 )) ”
  &&  “ (cap > 1073741823) ”
  &&  “ ((Zlength (l)) = cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((retval_2 + ((Zlength (l)) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.undef_missing_i retval_2 (Zlength (l)) cap actual )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> actual)
  **  (PtrArray.seg retval_2 0 cap l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval_2)
.

Definition vecp_push_partial_solve_wit_9 :=
forall (l: (@list Z)) (v_pre: Z) (p: Z) (cap: Z) (PreH1 : ((Zlength (l)) < cap)) (PreH2 : ((Zlength (l)) <> cap)) (PreH3 : (vec_buf_ok cap p )) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zlength (l)) <= cap)) (PreH6 : (0 <= (Zlength (l)))),
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  (PtrArray.undef_seg p (Zlength (l)) cap )
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
|--
  “ ((Zlength (l)) < cap) ”
  &&  “ ((Zlength (l)) <> cap) ”
  &&  “ (vec_buf_ok cap p ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  (((p + ((Zlength (l)) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.undef_seg p ((Zlength (l)) + 1 ) cap )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (l)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  (PtrArray.seg p 0 (Zlength (l)) l )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> p)
.

(*----- Function vecp_remove -----*)

Definition vecp_remove_safety_wit_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (retval: Z) (PreH1 : (retval = p)) (PreH2 : (In e_pre l )),
  ((( &( "j" ) )) # Int  |->_)
  **  (Vecp.rep_ptr v_pre p l )
  **  ((( &( "ws" ) )) # Ptr  |-> retval)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vecp_remove_safety_wit_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (PreH1 : ((Znth (j - 0 ) l 0) <> e_pre)) (PreH2 : (vec_buf_ok cap ws )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))) (PreH6 : (vecp_remove_scan_inv e_pre l j )) (PreH7 : (0 <= j)) (PreH8 : (j < (Zlength (l)))),
  (PtrArray.seg ws 0 (Zlength (l)) l )
  **  (PtrArray.undef_seg ws (Zlength (l)) cap )
  **  (Vecp.header v_pre ws (Zlength (l)) cap )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition vecp_remove_safety_wit_3 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (retval: Z) (PreH1 : (j >= retval)) (PreH2 : (retval = (Zlength (l)))) (PreH3 : ((Znth (j - 0 ) l 0) = e_pre)) (PreH4 : (vec_buf_ok cap ws )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))) (PreH8 : (vecp_remove_scan_inv e_pre l j )) (PreH9 : (0 <= j)) (PreH10 : (j < (Zlength (l)))),
  (Vecp.rep_ptr v_pre ws l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ False ”
.

Definition vecp_remove_safety_wit_4 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH3 : (0 <= j)) (PreH4 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((retval - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
) \/
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH3 : (0 <= j)) (PreH4 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((retval - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
).

Definition vecp_remove_safety_wit_4_split_goal_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH3 : (0 <= j)) (PreH4 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((retval - 1 ) <= INT_MAX) ”
.

Definition vecp_remove_safety_wit_4_split_goal_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH3 : (0 <= j)) (PreH4 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition vecp_remove_safety_wit_5 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH3 : (0 <= j)) (PreH4 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vecp_remove_safety_wit_6 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (cap: Z) (PreH1 : (vec_buf_ok cap ws )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (words_now)) <= cap)) (PreH4 : (0 <= (Zlength (words_now)))) (PreH5 : (j < (retval - 1 ))) (PreH6 : (retval = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (PtrArray.full ws (Zlength (words_now)) (replace_Znth (j) ((Znth ((j + 1 ) - 0 ) words_now 0)) (words_now)) )
  **  (PtrArray.undef_seg ws (Zlength (words_now)) cap )
  **  (Vecp.header v_pre ws (Zlength (words_now)) cap )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition vecp_remove_safety_wit_7 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (j < (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
) \/
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (j < (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
).

Definition vecp_remove_safety_wit_7_split_goal_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (j < (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((j + 1 ) <= INT_MAX) ”
.

Definition vecp_remove_safety_wit_7_split_goal_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (j < (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition vecp_remove_safety_wit_8 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (j < (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vecp_remove_safety_wit_9 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval_2: Z) (found: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (first_occurrence e_pre l found )) (PreH3 : (1 <= (Zlength (words_now)))) (PreH4 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH5 : (j >= (retval_2 - 1 ))) (PreH6 : (retval_2 = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((retval - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
) \/
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval_2: Z) (found: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (first_occurrence e_pre l found )) (PreH3 : (1 <= (Zlength (words_now)))) (PreH4 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH5 : (j >= (retval_2 - 1 ))) (PreH6 : (retval_2 = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((retval - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
).

Definition vecp_remove_safety_wit_9_split_goal_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval_2: Z) (found: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (first_occurrence e_pre l found )) (PreH3 : (1 <= (Zlength (words_now)))) (PreH4 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH5 : (j >= (retval_2 - 1 ))) (PreH6 : (retval_2 = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((retval - 1 ) <= INT_MAX) ”
.

Definition vecp_remove_safety_wit_9_split_goal_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval_2: Z) (found: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (first_occurrence e_pre l found )) (PreH3 : (1 <= (Zlength (words_now)))) (PreH4 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH5 : (j >= (retval_2 - 1 ))) (PreH6 : (retval_2 = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition vecp_remove_safety_wit_10 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval: Z) (found: Z) (words_now: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 = (Zlength (words_now)))) (PreH2 : (first_occurrence e_pre l found )) (PreH3 : (1 <= (Zlength (words_now)))) (PreH4 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH5 : (j >= (retval - 1 ))) (PreH6 : (retval = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vecp_remove_entail_wit_1 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (p: Z) (retval: Z) (PreH1 : (retval = p)) (PreH2 : (In e_pre l )),
  (Vecp.rep_ptr v_pre p l )
|--
  “ (vecp_remove_scan_inv e_pre l 0 ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < (Zlength (l))) ”
  &&  (Vecp.rep_ptr v_pre retval l )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (p: Z) (retval: Z) (PreH1 : (retval = p)) (PreH2 : (In e_pre l )),
  TT && emp 
|--
  “ (0 < (Zlength (l))) ”
  &&  “ (vecp_remove_scan_inv e_pre l 0 ) ”
  &&  emp
).

Definition vecp_remove_entail_wit_1_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (retval: Z) (PreH1 : (retval = p)) (PreH2 : (In e_pre l )),
  (0 < (Zlength (l)))
.

Definition vecp_remove_entail_wit_1_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (p: Z) (retval: Z) (PreH1 : (retval = p)) (PreH2 : (In e_pre l )),
  (vecp_remove_scan_inv e_pre l 0 )
.

Definition vecp_remove_entail_wit_2 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (PreH1 : ((Znth (j - 0 ) l 0) <> e_pre)) (PreH2 : (vec_buf_ok cap ws )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))) (PreH6 : (vecp_remove_scan_inv e_pre l j )) (PreH7 : (0 <= j)) (PreH8 : (j < (Zlength (l)))),
  (PtrArray.seg ws 0 (Zlength (l)) l )
  **  (PtrArray.undef_seg ws (Zlength (l)) cap )
  **  (Vecp.header v_pre ws (Zlength (l)) cap )
|--
  “ (vecp_remove_scan_inv e_pre l (j + 1 ) ) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) < (Zlength (l))) ”
  &&  (Vecp.rep_ptr v_pre ws l )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (PreH1 : ((Znth (j - 0 ) l 0) <> e_pre)) (PreH2 : (vec_buf_ok cap ws )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))) (PreH6 : (vecp_remove_scan_inv e_pre l j )) (PreH7 : (0 <= j)) (PreH8 : (j < (Zlength (l)))),
  TT && emp 
|--
  “ ((j + 1 ) < (Zlength (l))) ”
  &&  “ (vecp_remove_scan_inv e_pre l (j + 1 ) ) ”
  &&  emp
).

Definition vecp_remove_entail_wit_2_split_goal_1 :=
forall (l: (@list Z)) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (PreH1 : ((Znth (j - 0 ) l 0) <> e_pre)) (PreH2 : (vec_buf_ok cap ws )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))) (PreH6 : (vecp_remove_scan_inv e_pre l j )) (PreH7 : (0 <= j)) (PreH8 : (j < (Zlength (l)))),
  ((j + 1 ) < (Zlength (l)))
.

Definition vecp_remove_entail_wit_2_split_goal_2 :=
forall (l: (@list Z)) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (PreH1 : ((Znth (j - 0 ) l 0) <> e_pre)) (PreH2 : (vec_buf_ok cap ws )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))) (PreH6 : (vecp_remove_scan_inv e_pre l j )) (PreH7 : (0 <= j)) (PreH8 : (j < (Zlength (l)))),
  (vecp_remove_scan_inv e_pre l (j + 1 ) )
.

Definition vecp_remove_entail_wit_3 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (retval: Z) (PreH1 : (j < retval)) (PreH2 : (retval = (Zlength (l)))) (PreH3 : ((Znth (j - 0 ) l 0) = e_pre)) (PreH4 : (vec_buf_ok cap ws )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))) (PreH8 : (vecp_remove_scan_inv e_pre l j )) (PreH9 : (0 <= j)) (PreH10 : (j < (Zlength (l)))),
  (Vecp.rep_ptr v_pre ws l )
|--
  EX (found: Z) (words_now: (@list Z)),
  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  (Vecp.rep_ptr v_pre ws words_now )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (retval: Z) (PreH1 : (j < retval)) (PreH2 : (retval = (Zlength (l)))) (PreH3 : ((Znth (j - 0 ) l 0) = e_pre)) (PreH4 : (vec_buf_ok cap ws )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))) (PreH8 : (vecp_remove_scan_inv e_pre l j )) (PreH9 : (0 <= j)) (PreH10 : (j < (Zlength (l)))),
  TT && emp 
|--
  EX (found: Z),
  “ (vecp_remove_shift_inv (Znth (j - 0 ) l 0) l found j l ) ”
  &&  emp
).

Definition vecp_remove_entail_wit_4 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found_2: Z) (j: Z) (words_now_2: (@list Z)) (retval: Z) (cap: Z) (PreH1 : (vec_buf_ok cap ws )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (words_now_2)) <= cap)) (PreH4 : (0 <= (Zlength (words_now_2)))) (PreH5 : (j < (retval - 1 ))) (PreH6 : (retval = (Zlength (words_now_2)))) (PreH7 : (vecp_remove_shift_inv e_pre l found_2 j words_now_2 )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now_2)))),
  (PtrArray.full ws (Zlength (words_now_2)) (replace_Znth (j) ((Znth ((j + 1 ) - 0 ) words_now_2 0)) (words_now_2)) )
  **  (PtrArray.undef_seg ws (Zlength (words_now_2)) cap )
  **  (Vecp.header v_pre ws (Zlength (words_now_2)) cap )
|--
  EX (found: Z) (words_now: (@list Z)),
  “ (vecp_remove_shift_inv e_pre l found (j + 1 ) words_now ) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) < (Zlength (words_now))) ”
  &&  (Vecp.rep_ptr v_pre ws words_now )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (ws: Z) (found_2: Z) (j: Z) (words_now_2: (@list Z)) (retval: Z) (cap: Z) (PreH1 : (vec_buf_ok cap ws )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (words_now_2)) <= cap)) (PreH4 : (0 <= (Zlength (words_now_2)))) (PreH5 : (j < (retval - 1 ))) (PreH6 : (retval = (Zlength (words_now_2)))) (PreH7 : (vecp_remove_shift_inv e_pre l found_2 j words_now_2 )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now_2)))),
  TT && emp 
|--
  EX (found: Z),
  “ ((Zlength (words_now_2)) = (Zlength ((replace_Znth (j) ((Znth ((j + 1 ) - 0 ) words_now_2 0)) (words_now_2))))) ”
  &&  “ (vecp_remove_shift_inv e_pre l found (j + 1 ) (replace_Znth (j) ((Znth ((j + 1 ) - 0 ) words_now_2 0)) (words_now_2)) ) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) < (Zlength ((replace_Znth (j) ((Znth ((j + 1 ) - 0 ) words_now_2 0)) (words_now_2))))) ”
  &&  emp
).

Definition vecp_remove_return_wit_1 :=
(
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval: Z) (found: Z) (words_now: (@list Z)) (retval_2: Z) (PreH1 : ((Zlength ((sublist (0) ((retval_2 - 1 )) (words_now)))) = (retval_2 - 1 ))) (PreH2 : (retval_2 = (Zlength (words_now)))) (PreH3 : (first_occurrence e_pre l found )) (PreH4 : (1 <= (Zlength (words_now)))) (PreH5 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH6 : (j >= (retval - 1 ))) (PreH7 : (retval = (Zlength (words_now)))) (PreH8 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH9 : (0 <= j)) (PreH10 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws (sublist (0) ((retval_2 - 1 )) (words_now)) )
|--
  EX (k: Z),
  “ (first_occurrence e_pre l k ) ”
  &&  (Vecp.rep v_pre (remove_nth (k) (l)) )
) \/
(
forall (l: (@list Z)) (e_pre: Z) (j: Z) (retval: Z) (found: Z) (words_now: (@list Z)) (retval_2: Z) (PreH1 : ((Zlength ((sublist (0) ((retval_2 - 1 )) (words_now)))) = (retval_2 - 1 ))) (PreH2 : (retval_2 = (Zlength (words_now)))) (PreH3 : (first_occurrence e_pre l found )) (PreH4 : (1 <= (Zlength (words_now)))) (PreH5 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH6 : (j >= (retval - 1 ))) (PreH7 : (retval = (Zlength (words_now)))) (PreH8 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH9 : (0 <= j)) (PreH10 : (j < (Zlength (words_now)))),
  TT && emp 
|--
  EX (k: Z),
  “ ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (k) (l))) ”
  &&  “ (first_occurrence e_pre l k ) ”
  &&  emp
).

Definition vecp_remove_partial_solve_wit_1 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (PreH1 : (In e_pre l )),
  (Vecp.rep v_pre l )
|--
  EX (p: Z),
  “ (In e_pre l ) ”
  &&  (Vecp.rep_ptr v_pre p l )
.

Definition vecp_remove_partial_solve_wit_2 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (PreH1 : (vecp_remove_scan_inv e_pre l j )) (PreH2 : (0 <= j)) (PreH3 : (j < (Zlength (l)))),
  (Vecp.rep_ptr v_pre ws l )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap ws ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  “ (vecp_remove_scan_inv e_pre l j ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (l))) ”
  &&  (((ws + (j * sizeof(PTR)))) # Ptr  |-> (Znth (j - 0 ) l 0))
  **  (PtrArray.missing_i ws j 0 (Zlength (l)) l )
  **  (PtrArray.undef_seg ws (Zlength (l)) cap )
  **  (Vecp.header v_pre ws (Zlength (l)) cap )
.

Definition vecp_remove_partial_solve_wit_3 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (PreH1 : ((Znth (j - 0 ) l 0) = e_pre)) (PreH2 : (vec_buf_ok cap ws )) (PreH3 : (cap <= INT_MAX)) (PreH4 : ((Zlength (l)) <= cap)) (PreH5 : (0 <= (Zlength (l)))) (PreH6 : (vecp_remove_scan_inv e_pre l j )) (PreH7 : (0 <= j)) (PreH8 : (j < (Zlength (l)))),
  (PtrArray.seg ws 0 (Zlength (l)) l )
  **  (PtrArray.undef_seg ws (Zlength (l)) cap )
  **  (Vecp.header v_pre ws (Zlength (l)) cap )
|--
  “ ((Znth (j - 0 ) l 0) = e_pre) ”
  &&  “ (vec_buf_ok cap ws ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  “ (vecp_remove_scan_inv e_pre l j ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (l))) ”
  &&  (Vecp.rep_ptr v_pre ws l )
.

Definition vecp_remove_partial_solve_wit_4_pure :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (retval: Z) (PreH1 : (j < retval)) (PreH2 : (retval = (Zlength (l)))) (PreH3 : ((Znth (j - 0 ) l 0) = e_pre)) (PreH4 : (vec_buf_ok cap ws )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))) (PreH8 : (vecp_remove_scan_inv e_pre l j )) (PreH9 : (0 <= j)) (PreH10 : (j < (Zlength (l)))),
  (Vecp.rep_ptr v_pre ws l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ (1 <> 0) ”
.

Definition vecp_remove_partial_solve_wit_4_aux :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (cap: Z) (retval: Z) (PreH1 : (j < retval)) (PreH2 : (retval = (Zlength (l)))) (PreH3 : ((Znth (j - 0 ) l 0) = e_pre)) (PreH4 : (vec_buf_ok cap ws )) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zlength (l)) <= cap)) (PreH7 : (0 <= (Zlength (l)))) (PreH8 : (vecp_remove_scan_inv e_pre l j )) (PreH9 : (0 <= j)) (PreH10 : (j < (Zlength (l)))),
  (Vecp.rep_ptr v_pre ws l )
|--
  “ (1 <> 0) ”
  &&  “ (j < retval) ”
  &&  “ (retval = (Zlength (l))) ”
  &&  “ ((Znth (j - 0 ) l 0) = e_pre) ”
  &&  “ (vec_buf_ok cap ws ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (l)) <= cap) ”
  &&  “ (0 <= (Zlength (l))) ”
  &&  “ (vecp_remove_scan_inv e_pre l j ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (l))) ”
  &&  (Vecp.rep_ptr v_pre ws l )
.

Definition vecp_remove_partial_solve_wit_4 := vecp_remove_partial_solve_wit_4_pure -> vecp_remove_partial_solve_wit_4_aux.

Definition vecp_remove_partial_solve_wit_5 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (PreH1 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH2 : (0 <= j)) (PreH3 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
|--
  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  (Vecp.rep_ptr v_pre ws words_now )
.

Definition vecp_remove_partial_solve_wit_6 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (j < (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
|--
  EX (cap: Z),
  “ (vec_buf_ok cap ws ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (words_now)) <= cap) ”
  &&  “ (0 <= (Zlength (words_now))) ”
  &&  “ (j < (retval - 1 )) ”
  &&  “ (retval = (Zlength (words_now))) ”
  &&  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  (((ws + ((j + 1 ) * sizeof(PTR)))) # Ptr  |-> (Znth ((j + 1 ) - 0 ) words_now 0))
  **  (PtrArray.missing_i ws (j + 1 ) 0 (Zlength (words_now)) words_now )
  **  (PtrArray.undef_seg ws (Zlength (words_now)) cap )
  **  (Vecp.header v_pre ws (Zlength (words_now)) cap )
.

Definition vecp_remove_partial_solve_wit_7 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (found: Z) (j: Z) (words_now: (@list Z)) (retval: Z) (cap: Z) (PreH1 : (vec_buf_ok cap ws )) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (words_now)) <= cap)) (PreH4 : (0 <= (Zlength (words_now)))) (PreH5 : (j < (retval - 1 ))) (PreH6 : (retval = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (PtrArray.seg ws 0 (Zlength (words_now)) words_now )
  **  (PtrArray.undef_seg ws (Zlength (words_now)) cap )
  **  (Vecp.header v_pre ws (Zlength (words_now)) cap )
|--
  “ (vec_buf_ok cap ws ) ”
  &&  “ (cap <= INT_MAX) ”
  &&  “ ((Zlength (words_now)) <= cap) ”
  &&  “ (0 <= (Zlength (words_now))) ”
  &&  “ (j < (retval - 1 )) ”
  &&  “ (retval = (Zlength (words_now))) ”
  &&  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  (((ws + (j * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ws j 0 (Zlength (words_now)) words_now )
  **  (PtrArray.undef_seg ws (Zlength (words_now)) cap )
  **  (Vecp.header v_pre ws (Zlength (words_now)) cap )
.

Definition vecp_remove_partial_solve_wit_8_pure :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval: Z) (found: Z) (words_now: (@list Z)) (PreH1 : (j >= (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (j >= ((Zlength (words_now)) - 1 )) ”
  &&  “ (j < (Zlength (words_now))) ”
.

Definition vecp_remove_partial_solve_wit_8_aux :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval: Z) (found: Z) (words_now: (@list Z)) (PreH1 : (j >= (retval - 1 ))) (PreH2 : (retval = (Zlength (words_now)))) (PreH3 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH4 : (0 <= j)) (PreH5 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
|--
  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (j >= ((Zlength (words_now)) - 1 )) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  “ (j >= (retval - 1 )) ”
  &&  “ (retval = (Zlength (words_now))) ”
  &&  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  (Vecp.rep_ptr v_pre ws words_now )
.

Definition vecp_remove_partial_solve_wit_8 := vecp_remove_partial_solve_wit_8_pure -> vecp_remove_partial_solve_wit_8_aux.

Definition vecp_remove_partial_solve_wit_9 :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval: Z) (found: Z) (words_now: (@list Z)) (PreH1 : (first_occurrence e_pre l found )) (PreH2 : (1 <= (Zlength (words_now)))) (PreH3 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH4 : (j >= (retval - 1 ))) (PreH5 : (retval = (Zlength (words_now)))) (PreH6 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH7 : (0 <= j)) (PreH8 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
|--
  “ (first_occurrence e_pre l found ) ”
  &&  “ (1 <= (Zlength (words_now))) ”
  &&  “ ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l))) ”
  &&  “ (j >= (retval - 1 )) ”
  &&  “ (retval = (Zlength (words_now))) ”
  &&  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  (Vecp.rep_ptr v_pre ws words_now )
.

Definition vecp_remove_partial_solve_wit_10_pure :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval_2: Z) (found: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (first_occurrence e_pre l found )) (PreH3 : (1 <= (Zlength (words_now)))) (PreH4 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH5 : (j >= (retval_2 - 1 ))) (PreH6 : (retval_2 = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "ws" ) )) # Ptr  |-> ws)
|--
  “ (0 <= (retval - 1 )) ”
  &&  “ ((retval - 1 ) <= (Zlength (words_now))) ”
.

Definition vecp_remove_partial_solve_wit_10_aux :=
forall (l: (@list Z)) (v_pre: Z) (e_pre: Z) (ws: Z) (j: Z) (retval_2: Z) (found: Z) (words_now: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (words_now)))) (PreH2 : (first_occurrence e_pre l found )) (PreH3 : (1 <= (Zlength (words_now)))) (PreH4 : ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))) (PreH5 : (j >= (retval_2 - 1 ))) (PreH6 : (retval_2 = (Zlength (words_now)))) (PreH7 : (vecp_remove_shift_inv e_pre l found j words_now )) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength (words_now)))),
  (Vecp.rep_ptr v_pre ws words_now )
|--
  “ (0 <= (retval - 1 )) ”
  &&  “ ((retval - 1 ) <= (Zlength (words_now))) ”
  &&  “ (retval = (Zlength (words_now))) ”
  &&  “ (first_occurrence e_pre l found ) ”
  &&  “ (1 <= (Zlength (words_now))) ”
  &&  “ ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l))) ”
  &&  “ (j >= (retval_2 - 1 )) ”
  &&  “ (retval_2 = (Zlength (words_now))) ”
  &&  “ (vecp_remove_shift_inv e_pre l found j words_now ) ”
  &&  “ (0 <= j) ”
  &&  “ (j < (Zlength (words_now))) ”
  &&  (Vecp.rep_ptr v_pre ws words_now )
.

Definition vecp_remove_partial_solve_wit_10 := vecp_remove_partial_solve_wit_10_pure -> vecp_remove_partial_solve_wit_10_aux.

Definition vecp_remove_which_implies_wit_1 :=
(
forall (l: (@list Z)) (found: Z) (words_now: (@list Z)) (j: Z) (e: Z) (PreH1 : (vecp_remove_shift_inv e l found j words_now )) (PreH2 : (j >= ((Zlength (words_now)) - 1 ))) (PreH3 : (j < (Zlength (words_now)))),
  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (first_occurrence e l found ) ”
  &&  “ (1 <= (Zlength (words_now))) ”
  &&  “ ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (l: (@list Z)) (found: Z) (words_now: (@list Z)) (j: Z) (e: Z) (PreH1 : (vecp_remove_shift_inv e l found j words_now )) (PreH2 : (j >= ((Zlength (words_now)) - 1 ))) (PreH3 : (j < (Zlength (words_now)))),
  TT && emp 
|--
  “ ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l))) ”
  &&  “ (1 <= (Zlength (words_now))) ”
  &&  “ (first_occurrence e l found ) ”
  &&  emp
).

Definition vecp_remove_which_implies_wit_1_split_goal_1 :=
forall (l: (@list Z)) (found: Z) (words_now: (@list Z)) (j: Z) (e: Z) (PreH1 : (vecp_remove_shift_inv e l found j words_now )) (PreH2 : (j >= ((Zlength (words_now)) - 1 ))) (PreH3 : (j < (Zlength (words_now)))),
  ((sublist (0) (((Zlength (words_now)) - 1 )) (words_now)) = (remove_nth (found) (l)))
.

Definition vecp_remove_which_implies_wit_1_split_goal_2 :=
forall (l: (@list Z)) (found: Z) (words_now: (@list Z)) (j: Z) (e: Z) (PreH1 : (vecp_remove_shift_inv e l found j words_now )) (PreH2 : (j >= ((Zlength (words_now)) - 1 ))) (PreH3 : (j < (Zlength (words_now)))),
  (1 <= (Zlength (words_now)))
.

Definition vecp_remove_which_implies_wit_1_split_goal_3 :=
forall (l: (@list Z)) (found: Z) (words_now: (@list Z)) (j: Z) (e: Z) (PreH1 : (vecp_remove_shift_inv e l found j words_now )) (PreH2 : (j >= ((Zlength (words_now)) - 1 ))) (PreH3 : (j < (Zlength (words_now)))),
  (first_occurrence e l found )
.

Module Type VC_Correct.

Include vec_qcp_Strategy_Correct.

Axiom proof_of_veci_new_safety_wit_1 : veci_new_safety_wit_1.
Axiom proof_of_veci_new_safety_wit_2 : veci_new_safety_wit_2.
Axiom proof_of_veci_new_safety_wit_3 : veci_new_safety_wit_3.
Axiom proof_of_veci_new_return_wit_1 : veci_new_return_wit_1.
Axiom proof_of_veci_new_partial_solve_wit_1 : veci_new_partial_solve_wit_1.
Axiom proof_of_veci_delete_return_wit_1 : veci_delete_return_wit_1.
Axiom proof_of_veci_delete_partial_solve_wit_1 : veci_delete_partial_solve_wit_1.
Axiom proof_of_veci_delete_partial_solve_wit_2_pure : veci_delete_partial_solve_wit_2_pure.
Axiom proof_of_veci_delete_partial_solve_wit_2 : veci_delete_partial_solve_wit_2.
Axiom proof_of_veci_begin_return_wit_1 : veci_begin_return_wit_1.
Axiom proof_of_veci_begin_partial_solve_wit_1 : veci_begin_partial_solve_wit_1.
Axiom proof_of_veci_size_return_wit_1 : veci_size_return_wit_1.
Axiom proof_of_veci_size_partial_solve_wit_1 : veci_size_partial_solve_wit_1.
Axiom proof_of_veci_resize_return_wit_1 : veci_resize_return_wit_1.
Axiom proof_of_veci_resize_partial_solve_wit_1 : veci_resize_partial_solve_wit_1.
Axiom proof_of_vec_next_capacity_safety_wit_1 : vec_next_capacity_safety_wit_1.
Axiom proof_of_vec_next_capacity_safety_wit_2 : vec_next_capacity_safety_wit_2.
Axiom proof_of_vec_next_capacity_safety_wit_3 : vec_next_capacity_safety_wit_3.
Axiom proof_of_vec_next_capacity_safety_wit_4 : vec_next_capacity_safety_wit_4.
Axiom proof_of_vec_next_capacity_safety_wit_5 : vec_next_capacity_safety_wit_5.
Axiom proof_of_vec_next_capacity_safety_wit_6 : vec_next_capacity_safety_wit_6.
Axiom proof_of_vec_next_capacity_safety_wit_7 : vec_next_capacity_safety_wit_7.
Axiom proof_of_vec_next_capacity_safety_wit_8 : vec_next_capacity_safety_wit_8.
Axiom proof_of_vec_next_capacity_safety_wit_9 : vec_next_capacity_safety_wit_9.
Axiom proof_of_vec_next_capacity_return_wit_1 : vec_next_capacity_return_wit_1.
Axiom proof_of_vec_next_capacity_return_wit_2 : vec_next_capacity_return_wit_2.
Axiom proof_of_vec_next_capacity_partial_solve_wit_1 : vec_next_capacity_partial_solve_wit_1.
Axiom proof_of_veci_push_safety_wit_1 : veci_push_safety_wit_1.
Axiom proof_of_veci_push_safety_wit_2 : veci_push_safety_wit_2.
Axiom proof_of_veci_push_safety_wit_3 : veci_push_safety_wit_3.
Axiom proof_of_veci_push_safety_wit_4 : veci_push_safety_wit_4.
Axiom proof_of_veci_push_safety_wit_5 : veci_push_safety_wit_5.
Axiom proof_of_veci_push_entail_wit_1_1 : veci_push_entail_wit_1_1.
Axiom proof_of_veci_push_entail_wit_1_2 : veci_push_entail_wit_1_2.
Axiom proof_of_veci_push_entail_wit_1_3 : veci_push_entail_wit_1_3.
Axiom proof_of_veci_push_entail_wit_1_4 : veci_push_entail_wit_1_4.
Axiom proof_of_veci_push_entail_wit_1_5 : veci_push_entail_wit_1_5.
Axiom proof_of_veci_push_return_wit_1 : veci_push_return_wit_1.
Axiom proof_of_veci_push_return_wit_2 : veci_push_return_wit_2.
Axiom proof_of_veci_push_return_wit_3 : veci_push_return_wit_3.
Axiom proof_of_veci_push_return_wit_4 : veci_push_return_wit_4.
Axiom proof_of_veci_push_return_wit_5 : veci_push_return_wit_5.
Axiom proof_of_veci_push_partial_solve_wit_1 : veci_push_partial_solve_wit_1.
Axiom proof_of_veci_push_partial_solve_wit_2_pure : veci_push_partial_solve_wit_2_pure.
Axiom proof_of_veci_push_partial_solve_wit_2 : veci_push_partial_solve_wit_2.
Axiom proof_of_veci_push_partial_solve_wit_3_pure : veci_push_partial_solve_wit_3_pure.
Axiom proof_of_veci_push_partial_solve_wit_3 : veci_push_partial_solve_wit_3.
Axiom proof_of_veci_push_partial_solve_wit_4_pure : veci_push_partial_solve_wit_4_pure.
Axiom proof_of_veci_push_partial_solve_wit_4 : veci_push_partial_solve_wit_4.
Axiom proof_of_veci_push_partial_solve_wit_5 : veci_push_partial_solve_wit_5.
Axiom proof_of_veci_push_partial_solve_wit_6 : veci_push_partial_solve_wit_6.
Axiom proof_of_veci_push_partial_solve_wit_7 : veci_push_partial_solve_wit_7.
Axiom proof_of_veci_push_partial_solve_wit_8 : veci_push_partial_solve_wit_8.
Axiom proof_of_veci_push_partial_solve_wit_9 : veci_push_partial_solve_wit_9.
Axiom proof_of_vecp_new_safety_wit_1 : vecp_new_safety_wit_1.
Axiom proof_of_vecp_new_safety_wit_2 : vecp_new_safety_wit_2.
Axiom proof_of_vecp_new_return_wit_1 : vecp_new_return_wit_1.
Axiom proof_of_vecp_new_partial_solve_wit_1 : vecp_new_partial_solve_wit_1.
Axiom proof_of_vecp_new_partial_solve_wit_2_pure : vecp_new_partial_solve_wit_2_pure.
Axiom proof_of_vecp_new_partial_solve_wit_2 : vecp_new_partial_solve_wit_2.
Axiom proof_of_vecp_delete_return_wit_1 : vecp_delete_return_wit_1.
Axiom proof_of_vecp_delete_partial_solve_wit_1 : vecp_delete_partial_solve_wit_1.
Axiom proof_of_vecp_delete_partial_solve_wit_2_pure : vecp_delete_partial_solve_wit_2_pure.
Axiom proof_of_vecp_delete_partial_solve_wit_2 : vecp_delete_partial_solve_wit_2.
Axiom proof_of_vecp_begin_return_wit_1 : vecp_begin_return_wit_1.
Axiom proof_of_vecp_begin_partial_solve_wit_1 : vecp_begin_partial_solve_wit_1.
Axiom proof_of_vecp_size_return_wit_1 : vecp_size_return_wit_1.
Axiom proof_of_vecp_size_partial_solve_wit_1 : vecp_size_partial_solve_wit_1.
Axiom proof_of_vecp_resize_return_wit_1 : vecp_resize_return_wit_1.
Axiom proof_of_vecp_resize_partial_solve_wit_1 : vecp_resize_partial_solve_wit_1.
Axiom proof_of_vecp_push_safety_wit_1 : vecp_push_safety_wit_1.
Axiom proof_of_vecp_push_safety_wit_2 : vecp_push_safety_wit_2.
Axiom proof_of_vecp_push_safety_wit_3 : vecp_push_safety_wit_3.
Axiom proof_of_vecp_push_safety_wit_4 : vecp_push_safety_wit_4.
Axiom proof_of_vecp_push_safety_wit_5 : vecp_push_safety_wit_5.
Axiom proof_of_vecp_push_entail_wit_1_1 : vecp_push_entail_wit_1_1.
Axiom proof_of_vecp_push_entail_wit_1_2 : vecp_push_entail_wit_1_2.
Axiom proof_of_vecp_push_entail_wit_1_3 : vecp_push_entail_wit_1_3.
Axiom proof_of_vecp_push_entail_wit_1_4 : vecp_push_entail_wit_1_4.
Axiom proof_of_vecp_push_entail_wit_1_5 : vecp_push_entail_wit_1_5.
Axiom proof_of_vecp_push_return_wit_1 : vecp_push_return_wit_1.
Axiom proof_of_vecp_push_return_wit_2 : vecp_push_return_wit_2.
Axiom proof_of_vecp_push_return_wit_3 : vecp_push_return_wit_3.
Axiom proof_of_vecp_push_return_wit_4 : vecp_push_return_wit_4.
Axiom proof_of_vecp_push_return_wit_5 : vecp_push_return_wit_5.
Axiom proof_of_vecp_push_partial_solve_wit_1 : vecp_push_partial_solve_wit_1.
Axiom proof_of_vecp_push_partial_solve_wit_2_pure : vecp_push_partial_solve_wit_2_pure.
Axiom proof_of_vecp_push_partial_solve_wit_2 : vecp_push_partial_solve_wit_2.
Axiom proof_of_vecp_push_partial_solve_wit_3_pure : vecp_push_partial_solve_wit_3_pure.
Axiom proof_of_vecp_push_partial_solve_wit_3 : vecp_push_partial_solve_wit_3.
Axiom proof_of_vecp_push_partial_solve_wit_4_pure : vecp_push_partial_solve_wit_4_pure.
Axiom proof_of_vecp_push_partial_solve_wit_4 : vecp_push_partial_solve_wit_4.
Axiom proof_of_vecp_push_partial_solve_wit_5 : vecp_push_partial_solve_wit_5.
Axiom proof_of_vecp_push_partial_solve_wit_6 : vecp_push_partial_solve_wit_6.
Axiom proof_of_vecp_push_partial_solve_wit_7 : vecp_push_partial_solve_wit_7.
Axiom proof_of_vecp_push_partial_solve_wit_8 : vecp_push_partial_solve_wit_8.
Axiom proof_of_vecp_push_partial_solve_wit_9 : vecp_push_partial_solve_wit_9.
Axiom proof_of_vecp_remove_safety_wit_1 : vecp_remove_safety_wit_1.
Axiom proof_of_vecp_remove_safety_wit_2 : vecp_remove_safety_wit_2.
Axiom proof_of_vecp_remove_safety_wit_3 : vecp_remove_safety_wit_3.
Axiom proof_of_vecp_remove_safety_wit_4 : vecp_remove_safety_wit_4.
Axiom proof_of_vecp_remove_safety_wit_5 : vecp_remove_safety_wit_5.
Axiom proof_of_vecp_remove_safety_wit_6 : vecp_remove_safety_wit_6.
Axiom proof_of_vecp_remove_safety_wit_7 : vecp_remove_safety_wit_7.
Axiom proof_of_vecp_remove_safety_wit_8 : vecp_remove_safety_wit_8.
Axiom proof_of_vecp_remove_safety_wit_9 : vecp_remove_safety_wit_9.
Axiom proof_of_vecp_remove_safety_wit_10 : vecp_remove_safety_wit_10.
Axiom proof_of_vecp_remove_entail_wit_1 : vecp_remove_entail_wit_1.
Axiom proof_of_vecp_remove_entail_wit_2 : vecp_remove_entail_wit_2.
Axiom proof_of_vecp_remove_entail_wit_3 : vecp_remove_entail_wit_3.
Axiom proof_of_vecp_remove_entail_wit_4 : vecp_remove_entail_wit_4.
Axiom proof_of_vecp_remove_return_wit_1 : vecp_remove_return_wit_1.
Axiom proof_of_vecp_remove_partial_solve_wit_1 : vecp_remove_partial_solve_wit_1.
Axiom proof_of_vecp_remove_partial_solve_wit_2 : vecp_remove_partial_solve_wit_2.
Axiom proof_of_vecp_remove_partial_solve_wit_3 : vecp_remove_partial_solve_wit_3.
Axiom proof_of_vecp_remove_partial_solve_wit_4_pure : vecp_remove_partial_solve_wit_4_pure.
Axiom proof_of_vecp_remove_partial_solve_wit_4 : vecp_remove_partial_solve_wit_4.
Axiom proof_of_vecp_remove_partial_solve_wit_5 : vecp_remove_partial_solve_wit_5.
Axiom proof_of_vecp_remove_partial_solve_wit_6 : vecp_remove_partial_solve_wit_6.
Axiom proof_of_vecp_remove_partial_solve_wit_7 : vecp_remove_partial_solve_wit_7.
Axiom proof_of_vecp_remove_partial_solve_wit_8_pure : vecp_remove_partial_solve_wit_8_pure.
Axiom proof_of_vecp_remove_partial_solve_wit_8 : vecp_remove_partial_solve_wit_8.
Axiom proof_of_vecp_remove_partial_solve_wit_9 : vecp_remove_partial_solve_wit_9.
Axiom proof_of_vecp_remove_partial_solve_wit_10_pure : vecp_remove_partial_solve_wit_10_pure.
Axiom proof_of_vecp_remove_partial_solve_wit_10 : vecp_remove_partial_solve_wit_10.
Axiom proof_of_vecp_remove_which_implies_wit_1 : vecp_remove_which_implies_wit_1.

End VC_Correct.
