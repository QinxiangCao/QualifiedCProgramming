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
Require Import SimpleC.EE.Applications_human.mergeablelist.sll_project_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_strategy_goal.
From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_strategy_proof.

(*----- Function nil_list -----*)

Definition nil_list_safety_wit_1 := 
  TT && emp 
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition nil_list_return_wit_1 := 
  TT && emp 
|--
  (sll 0 (@nil Z) )
.

(*----- Function cons_list -----*)

Definition cons_list_return_wit_1 := 
forall (next_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) ,
  ((&((retval)  # "sll" ->ₛ "data")) # UInt  |-> data_pre)
  **  ((&((retval)  # "sll" ->ₛ "next")) # Ptr  |-> next_pre)
  **  (sll_pt next_pre pt l )
|--
  (EX (pt_new: Z) ,
  “ (l <> (@nil Z)) ” 
  &&  “ (pt_new = pt) ”
  &&  (sll_pt retval pt_new (cons (data_pre) (l)) ))
  ||
  (EX (pt_new: Z) ,
  “ (l = (@nil Z)) ” 
  &&  “ (pt_new = &((retval)  # "sll" ->ₛ "next")) ”
  &&  (sll_pt retval pt_new (cons (data_pre) (l)) ))
.

Definition cons_list_partial_solve_wit_1 := 
forall (next_pre: Z) (pt: Z) (l: (@list Z)) ,
  (sll_pt next_pre pt l )
|--
  (sll_pt next_pre pt l )
.

(*----- Function free_list -----*)

Definition free_list_entail_wit_1 := 
forall (head_pre: Z) (l: (@list Z)) ,
  (sll head_pre l )
|--
  EX (l_rest: (@list Z)) ,
  (sll head_pre l_rest )
.

Definition free_list_entail_wit_2 := 
forall (head: Z) (l_rest_2: (@list Z)) (head_next: Z) (head_data: Z) (l_rest_new: (@list Z)) (PreH1 : (l_rest_2 = (cons (head_data) (l_rest_new)))) (PreH2 : (head <> 0)) ,
  (sll head_next l_rest_new )
|--
  EX (l_rest: (@list Z)) ,
  (sll head_next l_rest )
.

Definition free_list_return_wit_1 := 
(
forall (head: Z) (l_rest: (@list Z)) (PreH1 : (head = 0)) ,
  (sll head l_rest )
|--
  TT && emp 
) \/
(
forall (head: Z) (l_rest: (@list Z)) (PreH1 : (head = 0)) ,
  (sll head l_rest )
|--
  TT && emp 
).

Definition free_list_return_wit_1_split_goal_spatial := 
forall (head: Z) (l_rest: (@list Z)) (PreH1 : (head = 0)) ,
  (sll head l_rest )
|--
  TT && emp 
.

Definition free_list_partial_solve_wit_1_pure := 
forall (head: Z) (l_rest: (@list Z)) (PreH1 : (head <> 0)) ,
  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sll head l_rest )
|--
  “ (head <> 0) ”
.

Definition free_list_partial_solve_wit_1_aux := 
forall (head: Z) (l_rest: (@list Z)) (PreH1 : (head <> 0)) ,
  (sll head l_rest )
|--
  “ (head <> 0) ” 
  &&  “ (head <> 0) ”
  &&  (sll head l_rest )
.

Definition free_list_partial_solve_wit_1 := free_list_partial_solve_wit_1_pure -> free_list_partial_solve_wit_1_aux.

Definition free_list_partial_solve_wit_2 := 
forall (head: Z) (l_rest: (@list Z)) (head_next: Z) (head_data: Z) (l_rest_new: (@list Z)) (PreH1 : (l_rest = (cons (head_data) (l_rest_new)))) (PreH2 : (head <> 0)) ,
  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
|--
  “ (l_rest = (cons (head_data) (l_rest_new))) ” 
  &&  “ (head <> 0) ”
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
.

Definition free_list_which_implies_wit_1 := 
(
forall (l_rest: (@list Z)) (head: Z) (PreH1 : (head <> 0)) ,
  (sll head l_rest )
|--
  EX (head_next: Z)  (head_data: Z)  (l_rest_new: (@list Z)) ,
  “ (l_rest = (cons (head_data) (l_rest_new))) ”
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
) \/
(
forall (l_rest: (@list Z)) (head: Z) (PreH1 : (head <> 0)) ,
  (sll head l_rest )
|--
  EX (head_next: Z)  (head_data: Z)  (l_rest_new: (@list Z)) ,
  “ (l_rest = (cons (head_data) (l_rest_new))) ”
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l_rest_new )
).

(*----- Function map_list -----*)

Definition map_list_safety_wit_1 := 
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg head_pre p (map_mult (x_pre) (l1)) )
  **  (sll p l2 )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition map_list_entail_wit_1 := 
(
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) ,
  (sll head_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ”
  &&  (sllseg head_pre head_pre (map_mult (x_pre) (l1)) )
  **  (sll head_pre l2 )
) \/
(
forall (x_pre: Z) (l: (@list Z)) ,
  TT && emp 
|--
  EX (l1: (@list Z)) ,
  “ ((map_mult (x_pre) (l1)) = (@nil Z)) ” 
  &&  “ (l = (app (l1) (l))) ”
  &&  emp
).

Definition map_list_entail_wit_2 := 
(
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l2_new: (@list Z)) (PreH1 : (l2_2 = (cons (p_data) (l2_new)))) (PreH2 : (p <> 0)) (PreH3 : (l = (app (l1_2) (l2_2)))) ,
  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> (unsigned_last_nbits ((x_pre * p_data )) (32)))
  **  (sllseg head_pre p (map_mult (x_pre) (l1_2)) )
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l2_new )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ”
  &&  (sllseg head_pre p_next (map_mult (x_pre) (l1)) )
  **  (sll p_next l2 )
) \/
(
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l2_new: (@list Z)) (PreH1 : ((unsigned_last_nbits ((x_pre * p_data )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((x_pre * p_data )) (32)) >= 0)) (PreH3 : (l2_2 = (cons (p_data) (l2_new)))) (PreH4 : (p <> 0)) (PreH5 : (l = (app (l1_2) (l2_2)))) ,
  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> (unsigned_last_nbits ((x_pre * p_data )) (32)))
  **  (sllseg head_pre p (map_mult (x_pre) (l1_2)) )
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l2_new))) ”
  &&  (sllseg head_pre p_next (map_mult (x_pre) (l1)) )
).

Definition map_list_return_wit_1 := 
(
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p = 0)) (PreH2 : (l = (app (l1) (l2)))) ,
  (sllseg head_pre p (map_mult (x_pre) (l1)) )
  **  (sll p l2 )
|--
  (sll head_pre (map_mult (x_pre) (l)) )
) \/
(
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p = 0)) (PreH2 : (l = (app (l1) (l2)))) ,
  (sllseg head_pre p (map_mult (x_pre) (l1)) )
  **  (sll p l2 )
|--
  (sll head_pre (map_mult (x_pre) (l)) )
).

Definition map_list_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p = 0)) (PreH2 : (l = (app (l1) (l2)))) ,
  (sllseg head_pre p (map_mult (x_pre) (l1)) )
  **  (sll p l2 )
|--
  (sll head_pre (map_mult (x_pre) (l)) )
.

Definition map_list_partial_solve_wit_1_pure := 
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p <> 0)) (PreH2 : (l = (app (l1) (l2)))) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg head_pre p (map_mult (x_pre) (l1)) )
  **  (sll p l2 )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (l = (app (l1) (l2))) ” 
  &&  “ (p <> 0) ”
.

Definition map_list_partial_solve_wit_1_aux := 
forall (x_pre: Z) (head_pre: Z) (l: (@list Z)) (p: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p <> 0)) (PreH2 : (l = (app (l1) (l2)))) ,
  (sllseg head_pre p (map_mult (x_pre) (l1)) )
  **  (sll p l2 )
|--
  “ (l = (app (l1) (l2))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ”
  &&  (sllseg head_pre p (map_mult (x_pre) (l1)) )
  **  (sll p l2 )
.

Definition map_list_partial_solve_wit_1 := map_list_partial_solve_wit_1_pure -> map_list_partial_solve_wit_1_aux.

Definition map_list_which_implies_wit_1 := 
(
forall (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (x: Z) (p: Z) (head: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (p <> 0)) ,
  (sllseg head p (map_mult (x) (l1)) )
  **  (sll p l2 )
|--
  EX (p_next: Z)  (p_data: Z)  (l2_new: (@list Z)) ,
  “ (l2 = (cons (p_data) (l2_new))) ”
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  (sllseg head p (map_mult (x) (l1)) )
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l2_new )
) \/
(
forall (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (p: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (p <> 0)) ,
  (sll p l2 )
|--
  EX (p_next: Z)  (p_data: Z)  (l2_new: (@list Z)) ,
  “ (l2 = (cons (p_data) (l2_new))) ”
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l2_new )
).

(*----- Function nil_list_box -----*)

Definition nil_list_box_return_wit_1 := 
forall (retval: Z) (retval_2: Z) (PreH1 : (retval <> 0)) ,
  (sll retval_2 (@nil Z) )
  **  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> &((retval)  # "sllb" ->ₛ "head"))
|--
  “ (retval <> 0) ”
  &&  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> 0)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> &((retval)  # "sllb" ->ₛ "head"))
.

Definition nil_list_box_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition nil_list_box_partial_solve_wit_2 := 
forall (retval: Z) (PreH1 : (retval <> 0)) ,
  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> 0)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
|--
  “ (retval <> 0) ”
  &&  ((&((retval)  # "sllb" ->ₛ "head")) # Ptr  |-> 0)
  **  ((&((retval)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
.

(*----- Function cons_list_box -----*)

Definition cons_list_box_safety_wit_1 := 
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (h: Z) (pt_new: Z) (retval: Z) (PreH1 : (l <> (@nil Z))) (PreH2 : (pt_new = pt)) (PreH3 : (box_pre <> 0)) (PreH4 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH5 : (l = (@nil Z))) ,
  (sll_pt retval pt_new (cons (data_pre) (l)) )
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((( &( "data" ) )) # UInt  |-> data_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  “ False ”
.

Definition cons_list_box_safety_wit_2 := 
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (h: Z) (pt_new: Z) (retval: Z) (PreH1 : (l = (@nil Z))) (PreH2 : (pt_new = &((retval)  # "sll" ->ₛ "next"))) (PreH3 : (box_pre <> 0)) (PreH4 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH5 : (l <> (@nil Z))) ,
  (sll_pt retval pt_new (cons (data_pre) (l)) )
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((( &( "data" ) )) # UInt  |-> data_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  “ False ”
.

Definition cons_list_box_safety_wit_3 := 
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new: Z) (retval: Z) (PreH1 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l <> (@nil Z))) (PreH3 : (pt_new = pt)) (PreH4 : (box_pre <> 0)) (PreH5 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l <> (@nil Z))) ,
  (sll_pt retval pt_new (cons (data_pre) (l)) )
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
  **  ((( &( "data" ) )) # UInt  |-> data_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  “ False ”
.

Definition cons_list_box_safety_wit_4 := 
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new: Z) (retval: Z) (PreH1 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l = (@nil Z))) (PreH3 : (pt_new = &((retval)  # "sll" ->ₛ "next"))) (PreH4 : (box_pre <> 0)) (PreH5 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l = (@nil Z))) ,
  (sll_pt retval pt_new (cons (data_pre) (l)) )
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
  **  ((( &( "data" ) )) # UInt  |-> data_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  “ False ”
.

Definition cons_list_box_return_wit_1 := 
(
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new_2: Z) (retval: Z) (PreH1 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l = (@nil Z))) (PreH3 : (pt_new_2 = &((retval)  # "sll" ->ₛ "next"))) (PreH4 : (box_pre <> 0)) (PreH5 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l = (@nil Z))) ,
  (sll_pt retval pt_new_2 (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> &((retval)  # "sll" ->ₛ "next"))
|--
  EX (pt_new: Z) ,
  “ (box_pre <> 0) ”
  &&  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt_new)
  **  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt_new (cons (data_pre) (l)) )
  **  ((pt_new) # Ptr  |-> 0)
) \/
(
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new_2: Z) (retval: Z) (PreH1 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l = (@nil Z))) (PreH3 : (pt_new_2 = &((retval)  # "sll" ->ₛ "next"))) (PreH4 : (box_pre <> 0)) (PreH5 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l = (@nil Z))) ,
  (sll_pt retval pt_new_2 (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
|--
  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") &((retval)  # "sll" ->ₛ "next") (cons (data_pre) (l)) )
  **  ((&((retval)  # "sll" ->ₛ "next")) # Ptr  |-> 0)
).

Definition cons_list_box_return_wit_1_split_goal_spatial := 
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new_2: Z) (retval: Z) (PreH1 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l = (@nil Z))) (PreH3 : (pt_new_2 = &((retval)  # "sll" ->ₛ "next"))) (PreH4 : (box_pre <> 0)) (PreH5 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l = (@nil Z))) ,
  (sll_pt retval pt_new_2 (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
|--
  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") &((retval)  # "sll" ->ₛ "next") (cons (data_pre) (l)) )
  **  ((&((retval)  # "sll" ->ₛ "next")) # Ptr  |-> 0)
.

Definition cons_list_box_return_wit_2 := 
(
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new_2: Z) (retval: Z) (PreH1 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l <> (@nil Z))) (PreH3 : (pt_new_2 = pt)) (PreH4 : (box_pre <> 0)) (PreH5 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l <> (@nil Z))) ,
  (sll_pt retval pt_new_2 (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  EX (pt_new: Z) ,
  “ (box_pre <> 0) ”
  &&  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt_new)
  **  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt_new (cons (data_pre) (l)) )
  **  ((pt_new) # Ptr  |-> 0)
) \/
(
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new_2: Z) (retval: Z) (PreH1 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l <> (@nil Z))) (PreH3 : (pt_new_2 = pt)) (PreH4 : (box_pre <> 0)) (PreH5 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l <> (@nil Z))) ,
  (sll_pt retval pt_new_2 (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
|--
  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt (cons (data_pre) (l)) )
  **  ((pt) # Ptr  |-> 0)
).

Definition cons_list_box_return_wit_2_split_goal_spatial := 
forall (box_pre: Z) (data_pre: Z) (pt: Z) (l: (@list Z)) (pt_new_2: Z) (retval: Z) (PreH1 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH2 : (l <> (@nil Z))) (PreH3 : (pt_new_2 = pt)) (PreH4 : (box_pre <> 0)) (PreH5 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH6 : (l <> (@nil Z))) ,
  (sll_pt retval pt_new_2 (cons (data_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> retval)
|--
  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt (cons (data_pre) (l)) )
  **  ((pt) # Ptr  |-> 0)
.

Definition cons_list_box_partial_solve_wit_1 := 
forall (box_pre: Z) (pt: Z) (l: (@list Z)) (PreH1 : (box_pre <> 0)) (PreH2 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH3 : (l <> (@nil Z))) ,
  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt l )
  **  ((pt) # Ptr  |-> 0)
|--
  “ (box_pre <> 0) ” 
  &&  “ (pt <> &((box_pre)  # "sllb" ->ₛ "head")) ” 
  &&  “ (l <> (@nil Z)) ”
  &&  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt l )
  **  ((pt) # Ptr  |-> 0)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition cons_list_box_partial_solve_wit_2 := 
forall (box_pre: Z) (pt: Z) (l: (@list Z)) (PreH1 : (box_pre <> 0)) (PreH2 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH3 : (l = (@nil Z))) ,
  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt l )
  **  ((pt) # Ptr  |-> 0)
|--
  “ (box_pre <> 0) ” 
  &&  “ (pt = &((box_pre)  # "sllb" ->ₛ "head")) ” 
  &&  “ (l = (@nil Z)) ”
  &&  (sllbseg &((box_pre)  # "sllb" ->ₛ "head") pt l )
  **  ((pt) # Ptr  |-> 0)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition cons_list_box_partial_solve_wit_3 := 
forall (box_pre: Z) (pt: Z) (l: (@list Z)) (h: Z) (PreH1 : (box_pre <> 0)) (PreH2 : (pt = &((box_pre)  # "sllb" ->ₛ "head"))) (PreH3 : (l = (@nil Z))) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  (sll_pt h pt l )
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  “ (box_pre <> 0) ” 
  &&  “ (pt = &((box_pre)  # "sllb" ->ₛ "head")) ” 
  &&  “ (l = (@nil Z)) ”
  &&  (sll_pt h pt l )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition cons_list_box_partial_solve_wit_4 := 
forall (box_pre: Z) (pt: Z) (l: (@list Z)) (h: Z) (PreH1 : (box_pre <> 0)) (PreH2 : (pt <> &((box_pre)  # "sllb" ->ₛ "head"))) (PreH3 : (l <> (@nil Z))) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  (sll_pt h pt l )
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  “ (box_pre <> 0) ” 
  &&  “ (pt <> &((box_pre)  # "sllb" ->ₛ "head")) ” 
  &&  “ (l <> (@nil Z)) ”
  &&  (sll_pt h pt l )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition cons_list_box_which_implies_wit_1 := 
(
forall (pt: Z) (l: (@list Z)) (box: Z) ,
  (sllbseg &((box)  # "sllb" ->ₛ "head") pt l )
  **  ((pt) # Ptr  |-> 0)
|--
  EX (h: Z) ,
  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  (sll_pt h pt l )
) \/
(
forall (pt: Z) (l: (@list Z)) (box: Z) ,
  (sllbseg &((box)  # "sllb" ->ₛ "head") pt l )
  **  ((pt) # Ptr  |-> 0)
|--
  EX (h: Z) ,
  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  (sll_pt h pt l )
).

(*----- Function map_list_box -----*)

Definition map_list_box_return_wit_1 := 
forall (x_pre: Z) (box_pre: Z) (l: (@list Z)) (h: Z) (PreH1 : (box_pre <> 0)) ,
  (sll h (map_mult (x_pre) (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
|--
  (sllb_sll box_pre (map_mult (x_pre) (l)) )
.

Definition map_list_box_partial_solve_wit_1 := 
forall (box_pre: Z) (l: (@list Z)) ,
  (sllb_sll box_pre l )
|--
  (sllb_sll box_pre l )
.

Definition map_list_box_partial_solve_wit_2 := 
forall (box_pre: Z) (l: (@list Z)) (h: Z) (PreH1 : (box_pre <> 0)) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
  **  (sll h l )
|--
  “ (box_pre <> 0) ”
  &&  (sll h l )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
.

Definition map_list_box_which_implies_wit_1 := 
forall (l: (@list Z)) (box: Z) ,
  (sllb_sll box l )
|--
  EX (h: Z) ,
  “ (box <> 0) ”
  &&  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
  **  (sll h l )
.

(*----- Function free_list_box -----*)

Definition free_list_box_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition free_list_box_partial_solve_wit_1 := 
forall (box_pre: Z) (l: (@list Z)) ,
  (sllb box_pre l )
|--
  (sllb box_pre l )
.

Definition free_list_box_partial_solve_wit_2 := 
forall (box_pre: Z) (l: (@list Z)) (pt: Z) (h: Z) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
|--
  (sll h l )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition free_list_box_partial_solve_wit_3 := 
forall (box_pre: Z) (pt: Z) (h: Z) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
|--
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
.

Definition free_list_box_which_implies_wit_1 := 
forall (l: (@list Z)) (box: Z) ,
  (sllb box l )
|--
  EX (pt: Z)  (h: Z) ,
  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt)
  **  (sll h l )
.

(*----- Function app_list_box -----*)

Definition app_list_box_safety_wit_1 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (b1_pre <> 0)) (PreH2 : (b2_pre <> 0)) ,
  ((( &( "pt2" ) )) # Ptr  |-> pt2)
  **  ((( &( "h2" ) )) # Ptr  |-> h2)
  **  ((( &( "b1" ) )) # Ptr  |-> b1_pre)
  **  ((( &( "b2" ) )) # Ptr  |-> b2_pre)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll_pt h2 pt2 l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition app_list_box_return_wit_1 := 
(
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 <> 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
) \/
(
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 <> 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
).

Definition app_list_box_return_wit_1_split_goal_spatial := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 <> 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
.

Definition app_list_box_return_wit_2 := 
(
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 = 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
) \/
(
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 = 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
).

Definition app_list_box_return_wit_2_split_goal_spatial := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 = 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
|--
  (sllb b1_pre (app (l1) (l2)) )
.

Definition app_list_box_partial_solve_wit_1 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  (sllb b1_pre l1 )
  **  (sllb b2_pre l2 )
|--
  (sllb b1_pre l1 )
  **  (sllb b2_pre l2 )
.

Definition app_list_box_partial_solve_wit_2 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 <> 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll_pt h2 pt2 l2 )
|--
  “ (h2 <> 0) ” 
  &&  “ (b1_pre <> 0) ” 
  &&  “ (b2_pre <> 0) ”
  &&  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
.

Definition app_list_box_partial_solve_wit_3 := 
forall (b2_pre: Z) (b1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (pt2: Z) (h2: Z) (pt1: Z) (PreH1 : (h2 = 0)) (PreH2 : (b1_pre <> 0)) (PreH3 : (b2_pre <> 0)) ,
  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll_pt h2 pt2 l2 )
|--
  “ (h2 = 0) ” 
  &&  “ (b1_pre <> 0) ” 
  &&  “ (b2_pre <> 0) ”
  &&  ((&((b2_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  ((&((b1_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1_pre)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> h2)
  **  (sll_pt h2 pt2 l2 )
.

Definition app_list_box_which_implies_wit_1 := 
(
forall (l2: (@list Z)) (l1: (@list Z)) (b1: Z) (b2: Z) ,
  (sllb b1 l1 )
  **  (sllb b2 l2 )
|--
  EX (pt2: Z)  (h2: Z)  (pt1: Z) ,
  “ (b1 <> 0) ” 
  &&  “ (b2 <> 0) ”
  &&  ((&((b1)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt1)
  **  (sllbseg &((b1)  # "sllb" ->ₛ "head") pt1 l1 )
  **  ((pt1) # Ptr  |-> 0)
  **  ((&((b2)  # "sllb" ->ₛ "head")) # Ptr  |-> h2)
  **  ((&((b2)  # "sllb" ->ₛ "ptail")) # Ptr  |-> pt2)
  **  (sll_pt h2 pt2 l2 )
) \/
(
forall (l2: (@list Z)) (l1: (@list Z)) (b1: Z) (b2: Z) (h_2: Z) (pt: Z) (h: Z) (pt_2: Z) (PreH1 : (b2 <> 0)) (PreH2 : (b1 <> 0)) ,
  (sll h l2 )
  **  (sll h_2 l1 )
  **  ((&((b1)  # "sllb" ->ₛ "head")) # Ptr  |-> h_2)
|--
  (sllbseg &((b1)  # "sllb" ->ₛ "head") pt l1 )
  **  ((pt) # Ptr  |-> 0)
  **  (sll_pt h pt_2 l2 )
).

Definition app_list_box_which_implies_wit_1_split_goal_spatial := 
forall (l2: (@list Z)) (l1: (@list Z)) (b1: Z) (b2: Z) (h_2: Z) (pt: Z) (h: Z) (pt_2: Z) (PreH1 : (b2 <> 0)) (PreH2 : (b1 <> 0)) ,
  (sll h l2 )
  **  (sll h_2 l1 )
  **  ((&((b1)  # "sllb" ->ₛ "head")) # Ptr  |-> h_2)
|--
  (sllbseg &((b1)  # "sllb" ->ₛ "head") pt l1 )
  **  ((pt) # Ptr  |-> 0)
  **  (sll_pt h pt_2 l2 )
.

(*----- Function sll_length -----*)

Definition sll_length_safety_wit_1 := 
forall (head_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "len" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  (sll head_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sll_length_entail_wit_1 := 
(
forall (head_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (sll head_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg head_pre head_pre l1 )
  **  (sll head_pre l2 )
) \/
(
forall (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ”
  &&  emp
).

Definition sll_length_entail_wit_1_split_goal_1 := 
forall (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (0 = (Zlength ((@nil Z))))
.

Definition sll_length_entail_wit_2 := 
(
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (head_next: Z) (head_data: Z) (l3: (@list Z)) (PreH1 : (l2_2 = (cons (head_data) (l3)))) (PreH2 : (l = (app (l1_2) (l2_2)))) (PreH3 : (len = (Zlength (l1_2)))) (PreH4 : ((Zlength (l)) <= INT_MAX)) (PreH5 : (head <> 0)) ,
  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l3 )
  **  (sllseg head_pre head l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((unsigned_last_nbits ((len + 1 )) (32)) = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg head_pre head_next l1 )
  **  (sll head_next l2 )
) \/
(
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (head_next: Z) (head_data: Z) (l3: (@list Z)) (PreH1 : (head_data <= UINT_MAX)) (PreH2 : (head_data >= 0)) (PreH3 : (l2_2 = (cons (head_data) (l3)))) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (len = (Zlength (l1_2)))) (PreH6 : ((Zlength (l)) <= INT_MAX)) (PreH7 : (head <> 0)) ,
  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sllseg head_pre head l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l3))) ” 
  &&  “ ((unsigned_last_nbits ((len + 1 )) (32)) = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg head_pre head_next l1 )
).

Definition sll_length_return_wit_1 := 
(
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (len = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (head = 0)) ,
  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  “ (len = (Zlength (l))) ”
  &&  (sll head_pre l )
) \/
(
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (len = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (head = 0)) ,
  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  “ (len = (Zlength (l))) ”
  &&  (sll head_pre l )
).

Definition sll_length_return_wit_1_split_goal_1 := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (len = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (head = 0)) ,
  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  “ (len = (Zlength (l))) ”
.

Definition sll_length_return_wit_1_split_goal_spatial := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (len = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (head = 0)) ,
  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  (sll head_pre l )
.

Definition sll_length_partial_solve_wit_1_pure := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (len = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (head <> 0)) ,
  ((( &( "len" ) )) # UInt  |-> len)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  “ (head <> 0) ”
.

Definition sll_length_partial_solve_wit_1_aux := 
forall (head_pre: Z) (l: (@list Z)) (head: Z) (len: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (len = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (head <> 0)) ,
  (sllseg head_pre head l1 )
  **  (sll head l2 )
|--
  “ (head <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (len = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ (head <> 0) ”
  &&  (sll head l2 )
  **  (sllseg head_pre head l1 )
.

Definition sll_length_partial_solve_wit_1 := sll_length_partial_solve_wit_1_pure -> sll_length_partial_solve_wit_1_aux.

Definition sll_length_which_implies_wit_1 := 
(
forall (l2: (@list Z)) (head: Z) (PreH1 : (head <> 0)) ,
  (sll head l2 )
|--
  EX (head_next: Z)  (head_data: Z)  (l3: (@list Z)) ,
  “ (l2 = (cons (head_data) (l3))) ”
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l3 )
) \/
(
forall (l2: (@list Z)) (head: Z) (PreH1 : (head <> 0)) ,
  (sll head l2 )
|--
  EX (head_next: Z)  (head_data: Z)  (l3: (@list Z)) ,
  “ (l2 = (cons (head_data) (l3))) ”
  &&  ((&((head)  # "sll" ->ₛ "data")) # UInt  |-> head_data)
  **  ((&((head)  # "sll" ->ₛ "next")) # Ptr  |-> head_next)
  **  (sll head_next l3 )
).

(*----- Function sll2array -----*)

Definition sll2array_safety_wit_1 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Zlength (l)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "i" ) )) # UInt  |->_)
  **  (UIntArray.undef_seg retval_2 0 retval )
  **  ((( &( "arr" ) )) # Ptr  |-> retval_2)
  **  (sll head_pre l )
  **  ((( &( "len" ) )) # UInt  |-> retval)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sll2array_safety_wit_2 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (i < len)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (len = (Zlength (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (retval = (Zlength (l)))) (PreH9 : ((Zlength (l)) <= INT_MAX)) (PreH10 : (p <> 0)) ,
  (UIntArray.seg_shape arr 0 (i + 1 ) )
  **  (UIntArray.undef_seg arr (i + 1 ) len )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "len" ) )) # UInt  |-> len)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sll2array_entail_wit_1 := 
(
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Zlength (l)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  (UIntArray.undef_seg retval_2 0 retval )
  **  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (retval = (Zlength (l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (Zlength (l))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg head_pre head_pre l1 )
  **  (sll head_pre l2 )
  **  (UIntArray.seg_shape retval_2 0 0 )
  **  (UIntArray.undef_seg retval_2 0 retval )
  **  ((out_array_pre) # Ptr  |->_)
) \/
(
forall (l: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (l)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= retval) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  emp
).

Definition sll2array_entail_wit_1_split_goal_1 := 
forall (l: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (l)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  (0 <= retval)
.

Definition sll2array_entail_wit_1_split_goal_2 := 
forall (l: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (l)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  (0 = (Zlength ((@nil Z))))
.

Definition sll2array_entail_wit_2 := 
(
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2_2 = (cons (p_data) (l3)))) (PreH2 : (i < len)) (PreH3 : (l = (app (l1_2) (l2_2)))) (PreH4 : (i = (Zlength (l1_2)))) (PreH5 : (len = (Zlength (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (retval = (Zlength (l)))) (PreH9 : ((Zlength (l)) <= INT_MAX)) (PreH10 : (p <> 0)) ,
  (UIntArray.seg_shape arr 0 (i + 1 ) )
  **  (UIntArray.undef_seg arr (i + 1 ) len )
  **  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1_2 )
  **  ((out_array_pre) # Ptr  |->_)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (len = (Zlength (l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (retval = (Zlength (l))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg head_pre p_next l1 )
  **  (sll p_next l2 )
  **  (UIntArray.seg_shape arr 0 (i + 1 ) )
  **  (UIntArray.undef_seg arr (i + 1 ) len )
  **  ((out_array_pre) # Ptr  |->_)
) \/
(
forall (head_pre: Z) (l: (@list Z)) (retval: Z) (p: Z) (len: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (p_data <= UINT_MAX)) (PreH2 : (p_data >= 0)) (PreH3 : (l2_2 = (cons (p_data) (l3)))) (PreH4 : (i < len)) (PreH5 : (l = (app (l1_2) (l2_2)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (len = (Zlength (l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (retval = (Zlength (l)))) (PreH11 : ((Zlength (l)) <= INT_MAX)) (PreH12 : (p <> 0)) ,
  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sllseg head_pre p l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l3))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (len = (Zlength (l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (retval = (Zlength (l))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg head_pre p_next l1 )
).

Definition sll2array_return_wit_1 := 
(
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (i = (Zlength (l1)))) (PreH3 : (len = (Zlength (l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (retval = (Zlength (l)))) (PreH7 : ((Zlength (l)) <= INT_MAX)) (PreH8 : (p = 0)) ,
  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
  **  ((out_array_pre) # Ptr  |-> arr)
|--
  EX (arr_ret: Z) ,
  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |-> arr_ret)
  **  (UIntArray.full_shape arr_ret (Zlength (l)) )
) \/
(
forall (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (i = (Zlength (l1)))) (PreH3 : (len = (Zlength (l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (retval = (Zlength (l)))) (PreH7 : ((Zlength (l)) <= INT_MAX)) (PreH8 : (p = 0)) ,
  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
|--
  (sll head_pre l )
  **  (UIntArray.full_shape arr (Zlength (l)) )
).

Definition sll2array_return_wit_1_split_goal_spatial := 
forall (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (i = (Zlength (l1)))) (PreH3 : (len = (Zlength (l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (retval = (Zlength (l)))) (PreH7 : ((Zlength (l)) <= INT_MAX)) (PreH8 : (p = 0)) ,
  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
|--
  (sll head_pre l )
  **  (UIntArray.full_shape arr (Zlength (l)) )
.

Definition sll2array_partial_solve_wit_1_pure := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "len" ) )) # UInt  |->_)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ ((Zlength (l)) <= INT_MAX) ”
.

Definition sll2array_partial_solve_wit_1_aux := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_partial_solve_wit_1 := sll2array_partial_solve_wit_1_pure -> sll2array_partial_solve_wit_1_aux.

Definition sll2array_partial_solve_wit_2_pure := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (l)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "arr" ) )) # Ptr  |->_)
  **  (sll head_pre l )
  **  ((( &( "len" ) )) # UInt  |-> retval)
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (retval = retval) ”
.

Definition sll2array_partial_solve_wit_2_aux := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (l)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (retval = (Zlength (l))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sll head_pre l )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_partial_solve_wit_2 := sll2array_partial_solve_wit_2_pure -> sll2array_partial_solve_wit_2_aux.

Definition sll2array_partial_solve_wit_3_pure := 
(
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (i = (Zlength (l1)))) (PreH3 : (len = (Zlength (l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (retval = (Zlength (l)))) (PreH7 : ((Zlength (l)) <= INT_MAX)) (PreH8 : (p <> 0)) ,
  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "len" ) )) # UInt  |-> len)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (l = (app (l1) (l2))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (i < len) ”
) \/
(
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (len <= UINT_MAX)) (PreH2 : (i <= UINT_MAX)) (PreH3 : (len >= 0)) (PreH4 : (i >= 0)) (PreH5 : (l = (app (l1) (l2)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (len = (Zlength (l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (retval = (Zlength (l)))) (PreH11 : ((Zlength (l)) <= INT_MAX)) (PreH12 : (p <> 0)) ,
  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "len" ) )) # UInt  |-> len)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (i < len) ”
).

Definition sll2array_partial_solve_wit_3_pure_split_goal_1 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (len <= UINT_MAX)) (PreH2 : (i <= UINT_MAX)) (PreH3 : (len >= 0)) (PreH4 : (i >= 0)) (PreH5 : (l = (app (l1) (l2)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (len = (Zlength (l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (retval = (Zlength (l)))) (PreH11 : ((Zlength (l)) <= INT_MAX)) (PreH12 : (p <> 0)) ,
  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "len" ) )) # UInt  |-> len)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (i < len) ”
.

Definition sll2array_partial_solve_wit_3_aux := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (i = (Zlength (l1)))) (PreH3 : (len = (Zlength (l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (retval = (Zlength (l)))) (PreH7 : ((Zlength (l)) <= INT_MAX)) (PreH8 : (p <> 0)) ,
  (sllseg head_pre p l1 )
  **  (sll p l2 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (l = (app (l1) (l2))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (i < len) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (len = (Zlength (l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (retval = (Zlength (l))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ (p <> 0) ”
  &&  (sll p l2 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_partial_solve_wit_3 := sll2array_partial_solve_wit_3_pure -> sll2array_partial_solve_wit_3_aux.

Definition sll2array_partial_solve_wit_4 := 
forall (out_array_pre: Z) (head_pre: Z) (l: (@list Z)) (retval: Z) (arr: Z) (p: Z) (len: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (i < len)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (len = (Zlength (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (retval = (Zlength (l)))) (PreH9 : ((Zlength (l)) <= INT_MAX)) (PreH10 : (p <> 0)) ,
  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ (l2 = (cons (p_data) (l3))) ” 
  &&  “ (i < len) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (len = (Zlength (l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (retval = (Zlength (l))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ (p <> 0) ”
  &&  (((arr + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg arr (i + 1 ) len )
  **  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.seg_shape arr 0 i )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sll2array_which_implies_wit_1 := 
(
forall (head_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (p: Z) (i: Z) (len: Z) (arr: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (p <> 0)) (PreH3 : (i < len)) ,
  (sll p l2 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
|--
  EX (p_next: Z)  (p_data: Z)  (l3: (@list Z)) ,
  “ (l2 = (cons (p_data) (l3))) ” 
  &&  “ (i < len) ”
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg head_pre p l1 )
  **  (UIntArray.seg_shape arr 0 i )
  **  (UIntArray.undef_seg arr i len )
) \/
(
forall (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (p: Z) (i: Z) (len: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (p <> 0)) (PreH3 : (i < len)) ,
  (sll p l2 )
|--
  EX (p_next: Z)  (p_data: Z)  (l3: (@list Z)) ,
  “ (l2 = (cons (p_data) (l3))) ” 
  &&  “ (i < len) ”
  &&  ((&((p)  # "sll" ->ₛ "data")) # UInt  |-> p_data)
  **  ((&((p)  # "sll" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
).

(*----- Function sllb2array -----*)

Definition sllb2array_return_wit_1 := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) (h: Z) (arr_ret_2: Z) (PreH1 : (box_pre <> 0)) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  (sll h l )
  **  ((out_array_pre) # Ptr  |-> arr_ret_2)
  **  (UIntArray.full_shape arr_ret_2 (Zlength (l)) )
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
|--
  EX (arr_ret: Z) ,
  (sllb_sll box_pre l )
  **  ((out_array_pre) # Ptr  |-> arr_ret)
  **  (UIntArray.full_shape arr_ret (Zlength (l)) )
.

Definition sllb2array_partial_solve_wit_1 := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (sllb_sll box_pre l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllb_sll box_pre l )
  **  ((out_array_pre) # Ptr  |->_)
.

Definition sllb2array_partial_solve_wit_2_pure := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) (h: Z) (PreH1 : (box_pre <> 0)) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
  **  (sll h l )
  **  ((( &( "out_array" ) )) # Ptr  |-> out_array_pre)
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ ((Zlength (l)) <= INT_MAX) ”
.

Definition sllb2array_partial_solve_wit_2_aux := 
forall (out_array_pre: Z) (box_pre: Z) (l: (@list Z)) (h: Z) (PreH1 : (box_pre <> 0)) (PreH2 : ((Zlength (l)) <= INT_MAX)) ,
  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
  **  (sll h l )
  **  ((out_array_pre) # Ptr  |->_)
|--
  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ (box_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sll h l )
  **  ((out_array_pre) # Ptr  |->_)
  **  ((&((box_pre)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box_pre)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
.

Definition sllb2array_partial_solve_wit_2 := sllb2array_partial_solve_wit_2_pure -> sllb2array_partial_solve_wit_2_aux.

Definition sllb2array_which_implies_wit_1 := 
forall (l: (@list Z)) (box: Z) ,
  (sllb_sll box l )
|--
  EX (h: Z) ,
  “ (box <> 0) ”
  &&  ((&((box)  # "sllb" ->ₛ "head")) # Ptr  |-> h)
  **  ((&((box)  # "sllb" ->ₛ "ptail")) # Ptr  |-> 0)
  **  (sll h l )
.

Module Type VC_Correct.

Include sll_project_Strategy_Correct.

Axiom proof_of_nil_list_safety_wit_1 : nil_list_safety_wit_1.
Axiom proof_of_nil_list_return_wit_1 : nil_list_return_wit_1.
Axiom proof_of_cons_list_return_wit_1 : cons_list_return_wit_1.
Axiom proof_of_cons_list_partial_solve_wit_1 : cons_list_partial_solve_wit_1.
Axiom proof_of_free_list_entail_wit_1 : free_list_entail_wit_1.
Axiom proof_of_free_list_entail_wit_2 : free_list_entail_wit_2.
Axiom proof_of_free_list_return_wit_1 : free_list_return_wit_1.
Axiom proof_of_free_list_partial_solve_wit_1_pure : free_list_partial_solve_wit_1_pure.
Axiom proof_of_free_list_partial_solve_wit_1 : free_list_partial_solve_wit_1.
Axiom proof_of_free_list_partial_solve_wit_2 : free_list_partial_solve_wit_2.
Axiom proof_of_free_list_which_implies_wit_1 : free_list_which_implies_wit_1.
Axiom proof_of_map_list_safety_wit_1 : map_list_safety_wit_1.
Axiom proof_of_map_list_entail_wit_1 : map_list_entail_wit_1.
Axiom proof_of_map_list_entail_wit_2 : map_list_entail_wit_2.
Axiom proof_of_map_list_return_wit_1 : map_list_return_wit_1.
Axiom proof_of_map_list_partial_solve_wit_1_pure : map_list_partial_solve_wit_1_pure.
Axiom proof_of_map_list_partial_solve_wit_1 : map_list_partial_solve_wit_1.
Axiom proof_of_map_list_which_implies_wit_1 : map_list_which_implies_wit_1.
Axiom proof_of_nil_list_box_return_wit_1 : nil_list_box_return_wit_1.
Axiom proof_of_nil_list_box_partial_solve_wit_1 : nil_list_box_partial_solve_wit_1.
Axiom proof_of_nil_list_box_partial_solve_wit_2 : nil_list_box_partial_solve_wit_2.
Axiom proof_of_cons_list_box_safety_wit_1 : cons_list_box_safety_wit_1.
Axiom proof_of_cons_list_box_safety_wit_2 : cons_list_box_safety_wit_2.
Axiom proof_of_cons_list_box_safety_wit_3 : cons_list_box_safety_wit_3.
Axiom proof_of_cons_list_box_safety_wit_4 : cons_list_box_safety_wit_4.
Axiom proof_of_cons_list_box_return_wit_1 : cons_list_box_return_wit_1.
Axiom proof_of_cons_list_box_return_wit_2 : cons_list_box_return_wit_2.
Axiom proof_of_cons_list_box_partial_solve_wit_1 : cons_list_box_partial_solve_wit_1.
Axiom proof_of_cons_list_box_partial_solve_wit_2 : cons_list_box_partial_solve_wit_2.
Axiom proof_of_cons_list_box_partial_solve_wit_3 : cons_list_box_partial_solve_wit_3.
Axiom proof_of_cons_list_box_partial_solve_wit_4 : cons_list_box_partial_solve_wit_4.
Axiom proof_of_cons_list_box_which_implies_wit_1 : cons_list_box_which_implies_wit_1.
Axiom proof_of_map_list_box_return_wit_1 : map_list_box_return_wit_1.
Axiom proof_of_map_list_box_partial_solve_wit_1 : map_list_box_partial_solve_wit_1.
Axiom proof_of_map_list_box_partial_solve_wit_2 : map_list_box_partial_solve_wit_2.
Axiom proof_of_map_list_box_which_implies_wit_1 : map_list_box_which_implies_wit_1.
Axiom proof_of_free_list_box_return_wit_1 : free_list_box_return_wit_1.
Axiom proof_of_free_list_box_partial_solve_wit_1 : free_list_box_partial_solve_wit_1.
Axiom proof_of_free_list_box_partial_solve_wit_2 : free_list_box_partial_solve_wit_2.
Axiom proof_of_free_list_box_partial_solve_wit_3 : free_list_box_partial_solve_wit_3.
Axiom proof_of_free_list_box_which_implies_wit_1 : free_list_box_which_implies_wit_1.
Axiom proof_of_app_list_box_safety_wit_1 : app_list_box_safety_wit_1.
Axiom proof_of_app_list_box_return_wit_1 : app_list_box_return_wit_1.
Axiom proof_of_app_list_box_return_wit_2 : app_list_box_return_wit_2.
Axiom proof_of_app_list_box_partial_solve_wit_1 : app_list_box_partial_solve_wit_1.
Axiom proof_of_app_list_box_partial_solve_wit_2 : app_list_box_partial_solve_wit_2.
Axiom proof_of_app_list_box_partial_solve_wit_3 : app_list_box_partial_solve_wit_3.
Axiom proof_of_app_list_box_which_implies_wit_1 : app_list_box_which_implies_wit_1.
Axiom proof_of_sll_length_safety_wit_1 : sll_length_safety_wit_1.
Axiom proof_of_sll_length_entail_wit_1 : sll_length_entail_wit_1.
Axiom proof_of_sll_length_entail_wit_2 : sll_length_entail_wit_2.
Axiom proof_of_sll_length_return_wit_1 : sll_length_return_wit_1.
Axiom proof_of_sll_length_partial_solve_wit_1_pure : sll_length_partial_solve_wit_1_pure.
Axiom proof_of_sll_length_partial_solve_wit_1 : sll_length_partial_solve_wit_1.
Axiom proof_of_sll_length_which_implies_wit_1 : sll_length_which_implies_wit_1.
Axiom proof_of_sll2array_safety_wit_1 : sll2array_safety_wit_1.
Axiom proof_of_sll2array_safety_wit_2 : sll2array_safety_wit_2.
Axiom proof_of_sll2array_entail_wit_1 : sll2array_entail_wit_1.
Axiom proof_of_sll2array_entail_wit_2 : sll2array_entail_wit_2.
Axiom proof_of_sll2array_return_wit_1 : sll2array_return_wit_1.
Axiom proof_of_sll2array_partial_solve_wit_1_pure : sll2array_partial_solve_wit_1_pure.
Axiom proof_of_sll2array_partial_solve_wit_1 : sll2array_partial_solve_wit_1.
Axiom proof_of_sll2array_partial_solve_wit_2_pure : sll2array_partial_solve_wit_2_pure.
Axiom proof_of_sll2array_partial_solve_wit_2 : sll2array_partial_solve_wit_2.
Axiom proof_of_sll2array_partial_solve_wit_3_pure : sll2array_partial_solve_wit_3_pure.
Axiom proof_of_sll2array_partial_solve_wit_3 : sll2array_partial_solve_wit_3.
Axiom proof_of_sll2array_partial_solve_wit_4 : sll2array_partial_solve_wit_4.
Axiom proof_of_sll2array_which_implies_wit_1 : sll2array_which_implies_wit_1.
Axiom proof_of_sllb2array_return_wit_1 : sllb2array_return_wit_1.
Axiom proof_of_sllb2array_partial_solve_wit_1 : sllb2array_partial_solve_wit_1.
Axiom proof_of_sllb2array_partial_solve_wit_2_pure : sllb2array_partial_solve_wit_2_pure.
Axiom proof_of_sllb2array_partial_solve_wit_2 : sllb2array_partial_solve_wit_2.
Axiom proof_of_sllb2array_which_implies_wit_1 : sllb2array_which_implies_wit_1.

End VC_Correct.
