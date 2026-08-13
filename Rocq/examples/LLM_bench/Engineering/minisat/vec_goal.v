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
Require Import vec_lib.
Local Open Scope sac.

(*----- Function veci_new -----*)

Definition veci_new_safety_wit_1 := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition veci_new_safety_wit_2 := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |->_)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition veci_new_return_wit_1 := 
(
forall (v_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (vec_alloc_ok sizeof(INT) 4 )) (PreH3 : (v_pre <> 0)) ,
  (IntArray.undef_full retval 4 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval)
|--
  EX (buf: Z) ,
  (veci_raw v_pre buf 4 (@nil Z) )
) \/
(
forall (v_pre: Z) (retval: Z) (PreH1 : (4 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (4 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (vec_alloc_ok sizeof(INT) 4 )) (PreH7 : (v_pre <> 0)) ,
  (IntArray.undef_full retval 4 )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval)
|--
  EX (buf: Z) ,
  (veci_raw v_pre buf 4 (@nil Z) )
).

Definition veci_new_partial_solve_wit_1 := 
forall (v_pre: Z) ,
  (veci_shell v_pre )
|--
  (veci_shell v_pre )
.

Definition veci_new_partial_solve_wit_2_pure := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (0 <= 4) ” 
  &&  “ ((4 * sizeof(INT) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(INT) * 4 ) = (4 * sizeof(INT) )) ”
.

Definition veci_new_partial_solve_wit_2_aux := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (0 <= 4) ” 
  &&  “ ((4 * sizeof(INT) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(INT) * 4 ) = (4 * sizeof(INT) )) ” 
  &&  “ (v_pre <> 0) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
.

Definition veci_new_partial_solve_wit_2 := veci_new_partial_solve_wit_2_pure -> veci_new_partial_solve_wit_2_aux.

Definition veci_new_which_implies_wit_1 := 
(
forall (v: Z) ,
  (veci_shell v )
|--
  “ (v <> 0) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |->_)
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |->_)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |->_)
) \/
(
forall (v: Z) ,
  (veci_shell v )
|--
  EX (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (v <> 0) ”
  &&  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> x_3)
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> x_2)
  **  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> x)
).

(*----- Function veci_delete -----*)

Definition veci_delete_return_wit_1 := 
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
|--
  (veci_shell v_pre )
) \/
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
|--
  (veci_shell v_pre )
).

Definition veci_delete_return_wit_1_split_goal_spatial := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
|--
  (veci_shell v_pre )
.

Definition veci_delete_partial_solve_wit_1 := 
forall (v_pre: Z) (xs: (@list Z)) ,
  (store_veci v_pre xs )
|--
  (store_veci v_pre xs )
.

Definition veci_delete_partial_solve_wit_2_pure := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ”
.

Definition veci_delete_partial_solve_wit_2_aux := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (v_pre <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
.

Definition veci_delete_partial_solve_wit_2 := veci_delete_partial_solve_wit_2_pure -> veci_delete_partial_solve_wit_2_aux.

Definition veci_delete_which_implies_wit_1 := 
(
forall (xs: (@list Z)) (v: Z) ,
  (store_veci v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (xs: (@list Z)) (v: Z) ,
  (store_veci v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
).

(*----- Function veci_begin -----*)

Definition veci_begin_return_wit_1 := 
(
forall (v_pre: Z) (xs: (@list Z)) (cap_2: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap_2)) (PreH5 : (4 <= cap_2)) (PreH6 : (cap_2 <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap_2 )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap_2 )
|--
  EX (cap: Z) ,
  (veci_raw v_pre buf cap xs )
) \/
(
forall (v_pre: Z) (xs: (@list Z)) (cap_2: Z) (buf: Z) (PreH1 : (cap_2 <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap_2 >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap_2)) (PreH9 : (4 <= cap_2)) (PreH10 : (cap_2 <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap_2 )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap_2 )
|--
  EX (cap: Z) ,
  (veci_raw v_pre buf cap xs )
).

Definition veci_begin_partial_solve_wit_1 := 
forall (v_pre: Z) (xs: (@list Z)) ,
  (store_veci v_pre xs )
|--
  (store_veci v_pre xs )
.

Definition veci_begin_which_implies_wit_1 := 
(
forall (xs: (@list Z)) (v: Z) ,
  (store_veci v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (xs: (@list Z)) (v: Z) ,
  (store_veci v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
).

(*----- Function veci_size -----*)

Definition veci_size_return_wit_1 := 
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ ((Zlength (xs)) = (Zlength (xs))) ”
  &&  (store_veci v_pre xs )
) \/
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  (store_veci v_pre xs )
).

Definition veci_size_return_wit_1_split_goal_spatial := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap )) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  (store_veci v_pre xs )
.

Definition veci_size_partial_solve_wit_1 := 
forall (v_pre: Z) (xs: (@list Z)) ,
  (store_veci v_pre xs )
|--
  (store_veci v_pre xs )
.

Definition veci_size_which_implies_wit_1 := 
(
forall (xs: (@list Z)) (v: Z) ,
  (store_veci v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (xs: (@list Z)) (v: Z) ,
  (store_veci v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
).

(*----- Function veci_resize -----*)

Definition veci_resize_return_wit_1 := 
(
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> k_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  (veci_raw v_pre buf cap (sublist (0) (k_pre) (xs)) )
) \/
(
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap )) (PreH12 : (0 <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> k_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  (veci_raw v_pre buf cap (sublist (0) (k_pre) (xs)) )
).

Definition veci_resize_return_wit_1_split_goal_spatial := 
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap )) (PreH12 : (0 <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> k_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  (veci_raw v_pre buf cap (sublist (0) (k_pre) (xs)) )
.

Definition veci_resize_partial_solve_wit_1 := 
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= (Zlength (xs)))) ,
  (veci_raw v_pre buf cap xs )
|--
  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= (Zlength (xs))) ”
  &&  (veci_raw v_pre buf cap xs )
.

Definition veci_resize_which_implies_wit_1 := 
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(INT) cap ) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (4 <= cap) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (v <> 0) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
).

Definition veci_resize_which_implies_wit_1_split_goal_1 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(INT) cap ) ”
.

Definition veci_resize_which_implies_wit_1_split_goal_2 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (cap <= INT_MAX) ”
.

Definition veci_resize_which_implies_wit_1_split_goal_3 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (4 <= cap) ”
.

Definition veci_resize_which_implies_wit_1_split_goal_4 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ ((Zlength (xs)) <= cap) ”
.

Definition veci_resize_which_implies_wit_1_split_goal_5 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (0 <= (Zlength (xs))) ”
.

Definition veci_resize_which_implies_wit_1_split_goal_6 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (buf <> 0) ”
.

Definition veci_resize_which_implies_wit_1_split_goal_7 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (v <> 0) ”
.

Definition veci_resize_which_implies_wit_1_split_goal_spatial := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
.

(*----- Function veci_push -----*)

Definition veci_push_safety_wit_1 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (((cap * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cap * 2 ) + 1 )) ”
.

Definition veci_push_safety_wit_2 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ ((cap * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cap * 2 )) ”
.

Definition veci_push_safety_wit_3 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition veci_push_safety_wit_4 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition veci_push_safety_wit_5 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (IntArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (((Zlength (xs)) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Zlength (xs)) + 1 )) ”
.

Definition veci_push_entail_wit_1_1 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (vec_alloc_ok sizeof(INT) ((cap * 2 ) + 1 ) )) (PreH3 : ((Zlength (xs)) = cap)) (PreH4 : (v_pre <> 0)) (PreH5 : (buf <> 0)) (PreH6 : (0 <= (Zlength (xs)))) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : (4 <= cap)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (vec_alloc_ok sizeof(INT) cap )) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  (IntArray.full retval (Zlength (xs)) xs )
  **  (IntArray.undef_seg retval (Zlength (xs)) ((cap * 2 ) + 1 ) )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> retval)
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (IntArray.full curbuf (Zlength (xs)) xs )
  **  (IntArray.undef_seg curbuf (Zlength (xs)) curcap )
.

Definition veci_push_entail_wit_1_2 := 
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (IntArray.full curbuf (Zlength (xs)) xs )
  **  (IntArray.undef_seg curbuf (Zlength (xs)) curcap )
) \/
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  TT && emp 
|--
  “ (((Zlength (xs)) < cap) -> ((buf = buf) /\ (cap = cap))) ” 
  &&  “ ((Zlength (xs)) < cap) ”
  &&  emp
).

Definition veci_push_entail_wit_1_2_split_goal_1 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  (((Zlength (xs)) < cap) -> ((buf = buf) /\ (cap = cap)))
.

Definition veci_push_entail_wit_1_2_split_goal_2 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((Zlength (xs)) < cap)
.

Definition veci_push_return_wit_1 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (curbuf_2: Z) (curcap_2: Z) (PreH1 : (vec_push_result (Zlength (xs)) buf cap curbuf_2 curcap_2 )) (PreH2 : (v_pre <> 0)) (PreH3 : (curbuf <> 0)) (PreH4 : (4 <= curcap)) (PreH5 : (curcap <= INT_MAX)) (PreH6 : (vec_alloc_ok sizeof(INT) curcap )) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : ((Zlength (xs)) < curcap)) (PreH9 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH10 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (veci_raw v_pre curbuf_2 curcap_2 (app (xs) ((cons (e_pre) ((@nil Z))))) )
|--
  EX (buf2: Z)  (cap2: Z) ,
  “ (vec_push_result (Zlength (xs)) buf cap buf2 cap2 ) ”
  &&  (veci_raw v_pre buf2 cap2 (app (xs) ((cons (e_pre) ((@nil Z))))) )
.

Definition veci_push_partial_solve_wit_1 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <= cap)) (PreH2 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  (veci_raw v_pre buf cap xs )
|--
  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX))) ”
  &&  (veci_raw v_pre buf cap xs )
.

Definition veci_push_partial_solve_wit_2_pure := 
(
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (cap <= ((cap * 2 ) + 1 )) ” 
  &&  “ ((((cap * 2 ) + 1 ) * sizeof(INT) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(INT) * ((cap * 2 ) + 1 ) ) = (((cap * 2 ) + 1 ) * sizeof(INT) )) ” 
  &&  “ (vec_alloc_ok sizeof(INT) ((cap * 2 ) + 1 ) ) ”
) \/
(
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (xs)) <= INT_MAX)) (PreH4 : (((cap * 2 ) + 1 ) <= INT_MAX)) (PreH5 : (e_pre >= INT_MIN)) (PreH6 : (cap >= INT_MIN)) (PreH7 : ((Zlength (xs)) >= INT_MIN)) (PreH8 : (((cap * 2 ) + 1 ) >= INT_MIN)) (PreH9 : ((Zlength (xs)) = cap)) (PreH10 : (v_pre <> 0)) (PreH11 : (buf <> 0)) (PreH12 : (0 <= (Zlength (xs)))) (PreH13 : ((Zlength (xs)) <= cap)) (PreH14 : (4 <= cap)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (vec_alloc_ok sizeof(INT) cap )) (PreH17 : ((Zlength (xs)) <= cap)) (PreH18 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (vec_alloc_ok sizeof(INT) ((cap * 2 ) + 1 ) ) ”
).

Definition veci_push_partial_solve_wit_2_pure_split_goal_1 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (xs)) <= INT_MAX)) (PreH4 : (((cap * 2 ) + 1 ) <= INT_MAX)) (PreH5 : (e_pre >= INT_MIN)) (PreH6 : (cap >= INT_MIN)) (PreH7 : ((Zlength (xs)) >= INT_MIN)) (PreH8 : (((cap * 2 ) + 1 ) >= INT_MIN)) (PreH9 : ((Zlength (xs)) = cap)) (PreH10 : (v_pre <> 0)) (PreH11 : (buf <> 0)) (PreH12 : (0 <= (Zlength (xs)))) (PreH13 : ((Zlength (xs)) <= cap)) (PreH14 : (4 <= cap)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (vec_alloc_ok sizeof(INT) cap )) (PreH17 : ((Zlength (xs)) <= cap)) (PreH18 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (vec_alloc_ok sizeof(INT) ((cap * 2 ) + 1 ) ) ”
.

Definition veci_push_partial_solve_wit_2_aux := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX)))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (cap <= ((cap * 2 ) + 1 )) ” 
  &&  “ ((((cap * 2 ) + 1 ) * sizeof(INT) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(INT) * ((cap * 2 ) + 1 ) ) = (((cap * 2 ) + 1 ) * sizeof(INT) )) ” 
  &&  “ (vec_alloc_ok sizeof(INT) ((cap * 2 ) + 1 ) ) ” 
  &&  “ ((Zlength (xs)) = cap) ” 
  &&  “ (v_pre <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(INT) ) <= UINT_MAX))) ”
  &&  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
.

Definition veci_push_partial_solve_wit_2 := veci_push_partial_solve_wit_2_pure -> veci_push_partial_solve_wit_2_aux.

Definition veci_push_partial_solve_wit_3 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (IntArray.full curbuf (Zlength (xs)) xs )
  **  (IntArray.undef_seg curbuf (Zlength (xs)) curcap )
|--
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  (((curbuf + ((Zlength (xs)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (IntArray.full curbuf (Zlength (xs)) xs )
.

Definition veci_push_partial_solve_wit_4_pure := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (IntArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
.

Definition veci_push_partial_solve_wit_4_aux := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (IntArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
|--
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ” 
  &&  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (IntArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
.

Definition veci_push_partial_solve_wit_4 := veci_push_partial_solve_wit_4_pure -> veci_push_partial_solve_wit_4_aux.

Definition veci_push_which_implies_wit_1 := 
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(INT) cap ) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(INT) cap ) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (4 <= cap) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (v <> 0) ”
  &&  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
).

Definition veci_push_which_implies_wit_1_split_goal_1 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(INT) cap ) ”
.

Definition veci_push_which_implies_wit_1_split_goal_2 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (cap <= INT_MAX) ”
.

Definition veci_push_which_implies_wit_1_split_goal_3 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (4 <= cap) ”
.

Definition veci_push_which_implies_wit_1_split_goal_4 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ ((Zlength (xs)) <= cap) ”
.

Definition veci_push_which_implies_wit_1_split_goal_5 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (0 <= (Zlength (xs))) ”
.

Definition veci_push_which_implies_wit_1_split_goal_6 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (buf <> 0) ”
.

Definition veci_push_which_implies_wit_1_split_goal_7 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  “ (v <> 0) ”
.

Definition veci_push_which_implies_wit_1_split_goal_spatial := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (veci_raw v buf cap xs )
|--
  ((&((v)  # "veci_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "veci_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (IntArray.full buf (Zlength (xs)) xs )
  **  (IntArray.undef_seg buf (Zlength (xs)) cap )
.

Definition veci_push_which_implies_wit_2 := 
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curcap_2: Z) (curbuf_2: Z) (e: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf_2 <> 0)) (PreH3 : (4 <= curcap_2)) (PreH4 : (curcap_2 <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap_2 )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap_2)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) /\ (curcap_2 = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap ) + 1 )))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap_2)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf_2)
  **  (IntArray.full curbuf_2 ((Zlength (xs)) + 1 ) (app (xs) ((cons (e) ((@nil Z))))) )
  **  (IntArray.undef_seg curbuf_2 ((Zlength (xs)) + 1 ) curcap_2 )
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap ) ”
  &&  (veci_raw v_pre curbuf curcap (app (xs) ((cons (e) ((@nil Z))))) )
) \/
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curcap_2: Z) (curbuf_2: Z) (e: Z) (PreH1 : (curcap_2 <= INT_MAX)) (PreH2 : (((Zlength (xs)) + 1 ) <= INT_MAX)) (PreH3 : (curcap_2 >= INT_MIN)) (PreH4 : (((Zlength (xs)) + 1 ) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (curbuf_2 <> 0)) (PreH7 : (4 <= curcap_2)) (PreH8 : (curcap_2 <= INT_MAX)) (PreH9 : (vec_alloc_ok sizeof(INT) curcap_2 )) (PreH10 : ((Zlength (xs)) <= cap)) (PreH11 : ((Zlength (xs)) < curcap_2)) (PreH12 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) /\ (curcap_2 = cap)))) (PreH13 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap ) + 1 )))) ,
  ((&((v_pre)  # "veci_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "veci_t" ->ₛ "cap")) # Int  |-> curcap_2)
  **  ((&((v_pre)  # "veci_t" ->ₛ "ptr")) # Ptr  |-> curbuf_2)
  **  (IntArray.full curbuf_2 ((Zlength (xs)) + 1 ) (app (xs) ((cons (e) ((@nil Z))))) )
  **  (IntArray.undef_seg curbuf_2 ((Zlength (xs)) + 1 ) curcap_2 )
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap ) ”
  &&  (veci_raw v_pre curbuf curcap (app (xs) ((cons (e) ((@nil Z))))) )
).

(*----- Function vecp_new -----*)

Definition vecp_new_safety_wit_1 := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vecp_new_safety_wit_2 := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |->_)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition vecp_new_return_wit_1 := 
(
forall (v_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (vec_alloc_ok sizeof(PTR) 4 )) (PreH3 : (v_pre <> 0)) ,
  (PtrArray.undef_full retval 4 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval)
|--
  EX (buf: Z) ,
  (vecp_raw v_pre buf 4 (@nil Z) )
) \/
(
forall (v_pre: Z) (retval: Z) (PreH1 : (4 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (4 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (vec_alloc_ok sizeof(PTR) 4 )) (PreH7 : (v_pre <> 0)) ,
  (PtrArray.undef_full retval 4 )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval)
|--
  EX (buf: Z) ,
  (vecp_raw v_pre buf 4 (@nil Z) )
).

Definition vecp_new_partial_solve_wit_1 := 
forall (v_pre: Z) ,
  (vecp_shell v_pre )
|--
  (vecp_shell v_pre )
.

Definition vecp_new_partial_solve_wit_2_pure := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (0 <= 4) ” 
  &&  “ ((4 * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * 4 ) = (4 * sizeof(PTR) )) ”
.

Definition vecp_new_partial_solve_wit_2_aux := 
forall (v_pre: Z) (PreH1 : (v_pre <> 0)) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
|--
  “ (0 <= 4) ” 
  &&  “ ((4 * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * 4 ) = (4 * sizeof(PTR) )) ” 
  &&  “ (v_pre <> 0) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> 0)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> 4)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
.

Definition vecp_new_partial_solve_wit_2 := vecp_new_partial_solve_wit_2_pure -> vecp_new_partial_solve_wit_2_aux.

Definition vecp_new_which_implies_wit_1 := 
(
forall (v: Z) ,
  (vecp_shell v )
|--
  “ (v <> 0) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |->_)
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |->_)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |->_)
) \/
(
forall (v: Z) ,
  (vecp_shell v )
|--
  EX (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (v <> 0) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> x_3)
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> x_2)
  **  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> x)
).

(*----- Function vecp_delete -----*)

Definition vecp_delete_return_wit_1 := 
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
|--
  (vecp_shell v_pre )
) \/
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
|--
  (vecp_shell v_pre )
).

Definition vecp_delete_return_wit_1_split_goal_spatial := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
|--
  (vecp_shell v_pre )
.

Definition vecp_delete_partial_solve_wit_1 := 
forall (v_pre: Z) (xs: (@list Z)) ,
  (store_vecp v_pre xs )
|--
  (store_vecp v_pre xs )
.

Definition vecp_delete_partial_solve_wit_2_pure := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ”
.

Definition vecp_delete_partial_solve_wit_2_aux := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (v_pre <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
.

Definition vecp_delete_partial_solve_wit_2 := vecp_delete_partial_solve_wit_2_pure -> vecp_delete_partial_solve_wit_2_aux.

Definition vecp_delete_which_implies_wit_1 := 
(
forall (xs: (@list Z)) (v: Z) ,
  (store_vecp v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (xs: (@list Z)) (v: Z) ,
  (store_vecp v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
).

(*----- Function vecp_begin -----*)

Definition vecp_begin_return_wit_1 := 
(
forall (v_pre: Z) (xs: (@list Z)) (cap_2: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap_2)) (PreH5 : (4 <= cap_2)) (PreH6 : (cap_2 <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap_2 )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap_2 )
|--
  EX (cap: Z) ,
  (vecp_raw v_pre buf cap xs )
) \/
(
forall (v_pre: Z) (xs: (@list Z)) (cap_2: Z) (buf: Z) (PreH1 : (cap_2 <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap_2 >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap_2)) (PreH9 : (4 <= cap_2)) (PreH10 : (cap_2 <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap_2 )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap_2 )
|--
  EX (cap: Z) ,
  (vecp_raw v_pre buf cap xs )
).

Definition vecp_begin_partial_solve_wit_1 := 
forall (v_pre: Z) (xs: (@list Z)) ,
  (store_vecp v_pre xs )
|--
  (store_vecp v_pre xs )
.

Definition vecp_begin_which_implies_wit_1 := 
(
forall (xs: (@list Z)) (v: Z) ,
  (store_vecp v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (xs: (@list Z)) (v: Z) ,
  (store_vecp v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
).

(*----- Function vecp_size -----*)

Definition vecp_size_return_wit_1 := 
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ ((Zlength (xs)) = (Zlength (xs))) ”
  &&  (store_vecp v_pre xs )
) \/
(
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  (store_vecp v_pre xs )
).

Definition vecp_size_return_wit_1_split_goal_spatial := 
forall (v_pre: Z) (xs: (@list Z)) (cap: Z) (buf: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap )) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  (store_vecp v_pre xs )
.

Definition vecp_size_partial_solve_wit_1 := 
forall (v_pre: Z) (xs: (@list Z)) ,
  (store_vecp v_pre xs )
|--
  (store_vecp v_pre xs )
.

Definition vecp_size_which_implies_wit_1 := 
(
forall (xs: (@list Z)) (v: Z) ,
  (store_vecp v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (xs: (@list Z)) (v: Z) ,
  (store_vecp v xs )
|--
  EX (cap: Z)  (buf: Z) ,
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
).

(*----- Function vecp_resize -----*)

Definition vecp_resize_return_wit_1 := 
(
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (v_pre <> 0)) (PreH2 : (buf <> 0)) (PreH3 : (0 <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> k_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  (vecp_raw v_pre buf cap (sublist (0) (k_pre) (xs)) )
) \/
(
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap )) (PreH12 : (0 <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> k_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  (vecp_raw v_pre buf cap (sublist (0) (k_pre) (xs)) )
).

Definition vecp_resize_return_wit_1_split_goal_spatial := 
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (buf <> 0)) (PreH7 : (0 <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap )) (PreH12 : (0 <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> k_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  (vecp_raw v_pre buf cap (sublist (0) (k_pre) (xs)) )
.

Definition vecp_resize_partial_solve_wit_1 := 
forall (k_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= (Zlength (xs)))) ,
  (vecp_raw v_pre buf cap xs )
|--
  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= (Zlength (xs))) ”
  &&  (vecp_raw v_pre buf cap xs )
.

Definition vecp_resize_which_implies_wit_1 := 
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(PTR) cap ) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (4 <= cap) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (v <> 0) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
).

Definition vecp_resize_which_implies_wit_1_split_goal_1 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(PTR) cap ) ”
.

Definition vecp_resize_which_implies_wit_1_split_goal_2 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (cap <= INT_MAX) ”
.

Definition vecp_resize_which_implies_wit_1_split_goal_3 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (4 <= cap) ”
.

Definition vecp_resize_which_implies_wit_1_split_goal_4 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ ((Zlength (xs)) <= cap) ”
.

Definition vecp_resize_which_implies_wit_1_split_goal_5 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (0 <= (Zlength (xs))) ”
.

Definition vecp_resize_which_implies_wit_1_split_goal_6 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (buf <> 0) ”
.

Definition vecp_resize_which_implies_wit_1_split_goal_7 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (v <> 0) ”
.

Definition vecp_resize_which_implies_wit_1_split_goal_spatial := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
.

(*----- Function vecp_push -----*)

Definition vecp_push_safety_wit_1 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (((cap * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cap * 2 ) + 1 )) ”
.

Definition vecp_push_safety_wit_2 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ ((cap * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cap * 2 )) ”
.

Definition vecp_push_safety_wit_3 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition vecp_push_safety_wit_4 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vecp_push_safety_wit_5 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (PtrArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (((Zlength (xs)) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Zlength (xs)) + 1 )) ”
.

Definition vecp_push_entail_wit_1_1 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (vec_alloc_ok sizeof(PTR) ((cap * 2 ) + 1 ) )) (PreH3 : ((Zlength (xs)) = cap)) (PreH4 : (v_pre <> 0)) (PreH5 : (buf <> 0)) (PreH6 : (0 <= (Zlength (xs)))) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : (4 <= cap)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (vec_alloc_ok sizeof(PTR) cap )) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  (PtrArray.full retval (Zlength (xs)) xs )
  **  (PtrArray.undef_seg retval (Zlength (xs)) ((cap * 2 ) + 1 ) )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> retval)
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (PtrArray.full curbuf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg curbuf (Zlength (xs)) curcap )
.

Definition vecp_push_entail_wit_1_2 := 
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (PtrArray.full curbuf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg curbuf (Zlength (xs)) curcap )
) \/
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  TT && emp 
|--
  “ (((Zlength (xs)) < cap) -> ((buf = buf) /\ (cap = cap))) ” 
  &&  “ ((Zlength (xs)) < cap) ”
  &&  emp
).

Definition vecp_push_entail_wit_1_2_split_goal_1 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  (((Zlength (xs)) < cap) -> ((buf = buf) /\ (cap = cap)))
.

Definition vecp_push_entail_wit_1_2_split_goal_2 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <> cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((Zlength (xs)) < cap)
.

Definition vecp_push_return_wit_1 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (curbuf_2: Z) (curcap_2: Z) (PreH1 : (vec_push_result (Zlength (xs)) buf cap curbuf_2 curcap_2 )) (PreH2 : (v_pre <> 0)) (PreH3 : (curbuf <> 0)) (PreH4 : (4 <= curcap)) (PreH5 : (curcap <= INT_MAX)) (PreH6 : (vec_alloc_ok sizeof(PTR) curcap )) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : ((Zlength (xs)) < curcap)) (PreH9 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH10 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (vecp_raw v_pre curbuf_2 curcap_2 (app (xs) ((cons (e_pre) ((@nil Z))))) )
|--
  EX (buf2: Z)  (cap2: Z) ,
  “ (vec_push_result (Zlength (xs)) buf cap buf2 cap2 ) ”
  &&  (vecp_raw v_pre buf2 cap2 (app (xs) ((cons (e_pre) ((@nil Z))))) )
.

Definition vecp_push_partial_solve_wit_1 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) <= cap)) (PreH2 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  (vecp_raw v_pre buf cap xs )
|--
  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX))) ”
  &&  (vecp_raw v_pre buf cap xs )
.

Definition vecp_push_partial_solve_wit_2_pure := 
(
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (cap <= ((cap * 2 ) + 1 )) ” 
  &&  “ ((((cap * 2 ) + 1 ) * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * ((cap * 2 ) + 1 ) ) = (((cap * 2 ) + 1 ) * sizeof(PTR) )) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) ((cap * 2 ) + 1 ) ) ”
) \/
(
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (((cap * 2 ) + 1 ) <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (xs)) >= INT_MIN)) (PreH6 : (((cap * 2 ) + 1 ) >= INT_MIN)) (PreH7 : ((Zlength (xs)) = cap)) (PreH8 : (v_pre <> 0)) (PreH9 : (buf <> 0)) (PreH10 : (0 <= (Zlength (xs)))) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (4 <= cap)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (vec_alloc_ok sizeof(PTR) cap )) (PreH15 : ((Zlength (xs)) <= cap)) (PreH16 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (vec_alloc_ok sizeof(PTR) ((cap * 2 ) + 1 ) ) ”
).

Definition vecp_push_partial_solve_wit_2_pure_split_goal_1 := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (((cap * 2 ) + 1 ) <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (xs)) >= INT_MIN)) (PreH6 : (((cap * 2 ) + 1 ) >= INT_MIN)) (PreH7 : ((Zlength (xs)) = cap)) (PreH8 : (v_pre <> 0)) (PreH9 : (buf <> 0)) (PreH10 : (0 <= (Zlength (xs)))) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (4 <= cap)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (vec_alloc_ok sizeof(PTR) cap )) (PreH15 : ((Zlength (xs)) <= cap)) (PreH16 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int  |-> ((cap * 2 ) + 1 ))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (vec_alloc_ok sizeof(PTR) ((cap * 2 ) + 1 ) ) ”
.

Definition vecp_push_partial_solve_wit_2_aux := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre <> 0)) (PreH3 : (buf <> 0)) (PreH4 : (0 <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap )) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX)))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
|--
  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (cap <= ((cap * 2 ) + 1 )) ” 
  &&  “ ((((cap * 2 ) + 1 ) * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * ((cap * 2 ) + 1 ) ) = (((cap * 2 ) + 1 ) * sizeof(PTR) )) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) ((cap * 2 ) + 1 ) ) ” 
  &&  “ ((Zlength (xs)) = cap) ” 
  &&  “ (v_pre <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap ) /\ (cap <= 1073741823)) /\ ((((2 * cap ) + 1 ) * sizeof(PTR) ) <= UINT_MAX))) ”
  &&  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
.

Definition vecp_push_partial_solve_wit_2 := vecp_push_partial_solve_wit_2_pure -> vecp_push_partial_solve_wit_2_aux.

Definition vecp_push_partial_solve_wit_3 := 
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (PtrArray.full curbuf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg curbuf (Zlength (xs)) curcap )
|--
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  (((curbuf + ((Zlength (xs)) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (PtrArray.full curbuf (Zlength (xs)) xs )
.

Definition vecp_push_partial_solve_wit_4_pure := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (PtrArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
|--
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
.

Definition vecp_push_partial_solve_wit_4_aux := 
forall (e_pre: Z) (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curbuf: Z) (curcap: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf <> 0)) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 )))) ,
  (PtrArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
  **  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
|--
  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ” 
  &&  “ (v_pre <> 0) ” 
  &&  “ (curbuf <> 0) ” 
  &&  “ (4 <= curcap) ” 
  &&  “ (curcap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) curcap ) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ ((Zlength (xs)) < curcap) ” 
  &&  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) /\ (curcap = cap))) ” 
  &&  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap ) + 1 ))) ”
  &&  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf)
  **  (PtrArray.full curbuf ((Zlength (xs)) + 1 ) (app (xs) ((cons (e_pre) ((@nil Z))))) )
  **  (PtrArray.undef_seg curbuf ((Zlength (xs)) + 1 ) curcap )
.

Definition vecp_push_partial_solve_wit_4 := vecp_push_partial_solve_wit_4_pure -> vecp_push_partial_solve_wit_4_aux.

Definition vecp_push_which_implies_wit_1 := 
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (v <> 0) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (4 <= cap) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (vec_alloc_ok sizeof(PTR) cap ) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
) \/
(
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(PTR) cap ) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (4 <= cap) ” 
  &&  “ ((Zlength (xs)) <= cap) ” 
  &&  “ (0 <= (Zlength (xs))) ” 
  &&  “ (buf <> 0) ” 
  &&  “ (v <> 0) ”
  &&  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
).

Definition vecp_push_which_implies_wit_1_split_goal_1 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (vec_alloc_ok sizeof(PTR) cap ) ”
.

Definition vecp_push_which_implies_wit_1_split_goal_2 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (cap <= INT_MAX) ”
.

Definition vecp_push_which_implies_wit_1_split_goal_3 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (4 <= cap) ”
.

Definition vecp_push_which_implies_wit_1_split_goal_4 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ ((Zlength (xs)) <= cap) ”
.

Definition vecp_push_which_implies_wit_1_split_goal_5 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (0 <= (Zlength (xs))) ”
.

Definition vecp_push_which_implies_wit_1_split_goal_6 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (buf <> 0) ”
.

Definition vecp_push_which_implies_wit_1_split_goal_7 := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  “ (v <> 0) ”
.

Definition vecp_push_which_implies_wit_1_split_goal_spatial := 
forall (cap: Z) (buf: Z) (xs: (@list Z)) (v: Z) ,
  (vecp_raw v buf cap xs )
|--
  ((&((v)  # "vecp_t" ->ₛ "size")) # Int  |-> (Zlength (xs)))
  **  ((&((v)  # "vecp_t" ->ₛ "cap")) # Int  |-> cap)
  **  ((&((v)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> buf)
  **  (PtrArray.full buf (Zlength (xs)) xs )
  **  (PtrArray.undef_seg buf (Zlength (xs)) cap )
.

Definition vecp_push_which_implies_wit_2 := 
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curcap_2: Z) (curbuf_2: Z) (e: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (curbuf_2 <> 0)) (PreH3 : (4 <= curcap_2)) (PreH4 : (curcap_2 <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap_2 )) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap_2)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) /\ (curcap_2 = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap ) + 1 )))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap_2)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf_2)
  **  (PtrArray.full curbuf_2 ((Zlength (xs)) + 1 ) (app (xs) ((cons (e) ((@nil Z))))) )
  **  (PtrArray.undef_seg curbuf_2 ((Zlength (xs)) + 1 ) curcap_2 )
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap ) ”
  &&  (vecp_raw v_pre curbuf curcap (app (xs) ((cons (e) ((@nil Z))))) )
) \/
(
forall (v_pre: Z) (cap: Z) (buf: Z) (xs: (@list Z)) (curcap_2: Z) (curbuf_2: Z) (e: Z) (PreH1 : (curcap_2 <= INT_MAX)) (PreH2 : (((Zlength (xs)) + 1 ) <= INT_MAX)) (PreH3 : (curcap_2 >= INT_MIN)) (PreH4 : (((Zlength (xs)) + 1 ) >= INT_MIN)) (PreH5 : (v_pre <> 0)) (PreH6 : (curbuf_2 <> 0)) (PreH7 : (4 <= curcap_2)) (PreH8 : (curcap_2 <= INT_MAX)) (PreH9 : (vec_alloc_ok sizeof(PTR) curcap_2 )) (PreH10 : ((Zlength (xs)) <= cap)) (PreH11 : ((Zlength (xs)) < curcap_2)) (PreH12 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) /\ (curcap_2 = cap)))) (PreH13 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap ) + 1 )))) ,
  ((&((v_pre)  # "vecp_t" ->ₛ "size")) # Int  |-> ((Zlength (xs)) + 1 ))
  **  ((&((v_pre)  # "vecp_t" ->ₛ "cap")) # Int  |-> curcap_2)
  **  ((&((v_pre)  # "vecp_t" ->ₛ "ptr")) # Ptr  |-> curbuf_2)
  **  (PtrArray.full curbuf_2 ((Zlength (xs)) + 1 ) (app (xs) ((cons (e) ((@nil Z))))) )
  **  (PtrArray.undef_seg curbuf_2 ((Zlength (xs)) + 1 ) curcap_2 )
|--
  EX (curbuf: Z)  (curcap: Z) ,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap ) ”
  &&  (vecp_raw v_pre curbuf curcap (app (xs) ((cons (e) ((@nil Z))))) )
).

Module Type VC_Correct.


Axiom proof_of_veci_new_safety_wit_1 : veci_new_safety_wit_1.
Axiom proof_of_veci_new_safety_wit_2 : veci_new_safety_wit_2.
Axiom proof_of_veci_new_return_wit_1 : veci_new_return_wit_1.
Axiom proof_of_veci_new_partial_solve_wit_1 : veci_new_partial_solve_wit_1.
Axiom proof_of_veci_new_partial_solve_wit_2_pure : veci_new_partial_solve_wit_2_pure.
Axiom proof_of_veci_new_partial_solve_wit_2 : veci_new_partial_solve_wit_2.
Axiom proof_of_veci_new_which_implies_wit_1 : veci_new_which_implies_wit_1.
Axiom proof_of_veci_delete_return_wit_1 : veci_delete_return_wit_1.
Axiom proof_of_veci_delete_partial_solve_wit_1 : veci_delete_partial_solve_wit_1.
Axiom proof_of_veci_delete_partial_solve_wit_2_pure : veci_delete_partial_solve_wit_2_pure.
Axiom proof_of_veci_delete_partial_solve_wit_2 : veci_delete_partial_solve_wit_2.
Axiom proof_of_veci_delete_which_implies_wit_1 : veci_delete_which_implies_wit_1.
Axiom proof_of_veci_begin_return_wit_1 : veci_begin_return_wit_1.
Axiom proof_of_veci_begin_partial_solve_wit_1 : veci_begin_partial_solve_wit_1.
Axiom proof_of_veci_begin_which_implies_wit_1 : veci_begin_which_implies_wit_1.
Axiom proof_of_veci_size_return_wit_1 : veci_size_return_wit_1.
Axiom proof_of_veci_size_partial_solve_wit_1 : veci_size_partial_solve_wit_1.
Axiom proof_of_veci_size_which_implies_wit_1 : veci_size_which_implies_wit_1.
Axiom proof_of_veci_resize_return_wit_1 : veci_resize_return_wit_1.
Axiom proof_of_veci_resize_partial_solve_wit_1 : veci_resize_partial_solve_wit_1.
Axiom proof_of_veci_resize_which_implies_wit_1 : veci_resize_which_implies_wit_1.
Axiom proof_of_veci_push_safety_wit_1 : veci_push_safety_wit_1.
Axiom proof_of_veci_push_safety_wit_2 : veci_push_safety_wit_2.
Axiom proof_of_veci_push_safety_wit_3 : veci_push_safety_wit_3.
Axiom proof_of_veci_push_safety_wit_4 : veci_push_safety_wit_4.
Axiom proof_of_veci_push_safety_wit_5 : veci_push_safety_wit_5.
Axiom proof_of_veci_push_entail_wit_1_1 : veci_push_entail_wit_1_1.
Axiom proof_of_veci_push_entail_wit_1_2 : veci_push_entail_wit_1_2.
Axiom proof_of_veci_push_return_wit_1 : veci_push_return_wit_1.
Axiom proof_of_veci_push_partial_solve_wit_1 : veci_push_partial_solve_wit_1.
Axiom proof_of_veci_push_partial_solve_wit_2_pure : veci_push_partial_solve_wit_2_pure.
Axiom proof_of_veci_push_partial_solve_wit_2 : veci_push_partial_solve_wit_2.
Axiom proof_of_veci_push_partial_solve_wit_3 : veci_push_partial_solve_wit_3.
Axiom proof_of_veci_push_partial_solve_wit_4_pure : veci_push_partial_solve_wit_4_pure.
Axiom proof_of_veci_push_partial_solve_wit_4 : veci_push_partial_solve_wit_4.
Axiom proof_of_veci_push_which_implies_wit_1 : veci_push_which_implies_wit_1.
Axiom proof_of_veci_push_which_implies_wit_2 : veci_push_which_implies_wit_2.
Axiom proof_of_vecp_new_safety_wit_1 : vecp_new_safety_wit_1.
Axiom proof_of_vecp_new_safety_wit_2 : vecp_new_safety_wit_2.
Axiom proof_of_vecp_new_return_wit_1 : vecp_new_return_wit_1.
Axiom proof_of_vecp_new_partial_solve_wit_1 : vecp_new_partial_solve_wit_1.
Axiom proof_of_vecp_new_partial_solve_wit_2_pure : vecp_new_partial_solve_wit_2_pure.
Axiom proof_of_vecp_new_partial_solve_wit_2 : vecp_new_partial_solve_wit_2.
Axiom proof_of_vecp_new_which_implies_wit_1 : vecp_new_which_implies_wit_1.
Axiom proof_of_vecp_delete_return_wit_1 : vecp_delete_return_wit_1.
Axiom proof_of_vecp_delete_partial_solve_wit_1 : vecp_delete_partial_solve_wit_1.
Axiom proof_of_vecp_delete_partial_solve_wit_2_pure : vecp_delete_partial_solve_wit_2_pure.
Axiom proof_of_vecp_delete_partial_solve_wit_2 : vecp_delete_partial_solve_wit_2.
Axiom proof_of_vecp_delete_which_implies_wit_1 : vecp_delete_which_implies_wit_1.
Axiom proof_of_vecp_begin_return_wit_1 : vecp_begin_return_wit_1.
Axiom proof_of_vecp_begin_partial_solve_wit_1 : vecp_begin_partial_solve_wit_1.
Axiom proof_of_vecp_begin_which_implies_wit_1 : vecp_begin_which_implies_wit_1.
Axiom proof_of_vecp_size_return_wit_1 : vecp_size_return_wit_1.
Axiom proof_of_vecp_size_partial_solve_wit_1 : vecp_size_partial_solve_wit_1.
Axiom proof_of_vecp_size_which_implies_wit_1 : vecp_size_which_implies_wit_1.
Axiom proof_of_vecp_resize_return_wit_1 : vecp_resize_return_wit_1.
Axiom proof_of_vecp_resize_partial_solve_wit_1 : vecp_resize_partial_solve_wit_1.
Axiom proof_of_vecp_resize_which_implies_wit_1 : vecp_resize_which_implies_wit_1.
Axiom proof_of_vecp_push_safety_wit_1 : vecp_push_safety_wit_1.
Axiom proof_of_vecp_push_safety_wit_2 : vecp_push_safety_wit_2.
Axiom proof_of_vecp_push_safety_wit_3 : vecp_push_safety_wit_3.
Axiom proof_of_vecp_push_safety_wit_4 : vecp_push_safety_wit_4.
Axiom proof_of_vecp_push_safety_wit_5 : vecp_push_safety_wit_5.
Axiom proof_of_vecp_push_entail_wit_1_1 : vecp_push_entail_wit_1_1.
Axiom proof_of_vecp_push_entail_wit_1_2 : vecp_push_entail_wit_1_2.
Axiom proof_of_vecp_push_return_wit_1 : vecp_push_return_wit_1.
Axiom proof_of_vecp_push_partial_solve_wit_1 : vecp_push_partial_solve_wit_1.
Axiom proof_of_vecp_push_partial_solve_wit_2_pure : vecp_push_partial_solve_wit_2_pure.
Axiom proof_of_vecp_push_partial_solve_wit_2 : vecp_push_partial_solve_wit_2.
Axiom proof_of_vecp_push_partial_solve_wit_3 : vecp_push_partial_solve_wit_3.
Axiom proof_of_vecp_push_partial_solve_wit_4_pure : vecp_push_partial_solve_wit_4_pure.
Axiom proof_of_vecp_push_partial_solve_wit_4 : vecp_push_partial_solve_wit_4.
Axiom proof_of_vecp_push_which_implies_wit_1 : vecp_push_which_implies_wit_1.
Axiom proof_of_vecp_push_which_implies_wit_2 : vecp_push_which_implies_wit_2.

End VC_Correct.
