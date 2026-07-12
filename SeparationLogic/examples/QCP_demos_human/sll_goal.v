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
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_proof.

(*----- Function length -----*)

Definition length_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition length_safety_wit_2 := 
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (n = (Zlength (l1)))) (PreH4 : ((Zlength (l)) <= INT_MAX)) (PreH5 : (p <> 0)) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (sllseg p_pre p l1 )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
) \/
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (n = (Zlength (l1)))) (PreH4 : ((Zlength (l)) <= INT_MAX)) (PreH5 : (p <> 0)) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (sllseg p_pre p l1 )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
).

Definition length_safety_wit_2_split_goal_1 := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (n = (Zlength (l1)))) (PreH4 : ((Zlength (l)) <= INT_MAX)) (PreH5 : (p <> 0)) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (sllseg p_pre p l1 )
|--
  “ ((n + 1 ) <= INT_MAX) ”
.

Definition length_safety_wit_2_split_goal_2 := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (n = (Zlength (l1)))) (PreH4 : ((Zlength (l)) <= INT_MAX)) (PreH5 : (p <> 0)) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (sllseg p_pre p l1 )
|--
  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition length_entail_wit_1 := 
(
forall (p_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg p_pre p_pre l1 )
  **  (sll p_pre l2 )
) \/
(
forall (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (l = (app ((@nil Z)) (l))) ”
  &&  emp
).

Definition length_entail_wit_1_split_goal_1 := 
forall (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (0 = (Zlength ((@nil Z))))
.

Definition length_entail_wit_1_split_goal_2 := 
forall (l: (@list Z)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (l = (app ((@nil Z)) (l)))
.

Definition length_entail_wit_2 := 
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2_2 = (cons (p_data) (l3)))) (PreH2 : (l = (app (l1_2) (l2_2)))) (PreH3 : (n = (Zlength (l1_2)))) (PreH4 : ((Zlength (l)) <= INT_MAX)) (PreH5 : (p <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg p_pre p l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((n + 1 ) = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg p_pre p_next l1 )
  **  (sll p_next l2 )
) \/
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (p_data <= INT_MAX)) (PreH2 : (p_data >= INT_MIN)) (PreH3 : (l2_2 = (cons (p_data) (l3)))) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (n = (Zlength (l1_2)))) (PreH6 : ((Zlength (l)) <= INT_MAX)) (PreH7 : (p <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sllseg p_pre p l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l3))) ” 
  &&  “ ((n + 1 ) = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  (sllseg p_pre p_next l1 )
).

Definition length_return_wit_1 := 
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (n = (Zlength (l))) ”
  &&  (sll p_pre l )
) \/
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (n = (Zlength (l))) ”
  &&  (sll p_pre l )
).

Definition length_return_wit_1_split_goal_1 := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (n = (Zlength (l))) ”
.

Definition length_return_wit_1_split_goal_spatial := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  (sll p_pre l )
.

Definition length_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (p <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (p <> 0) ”
.

Definition length_partial_solve_wit_1_aux := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : ((Zlength (l)) <= INT_MAX)) (PreH4 : (p <> 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (p <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (n = (Zlength (l1))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ (p <> 0) ”
  &&  (sll p l2 )
  **  (sllseg p_pre p l1 )
.

Definition length_partial_solve_wit_1 := length_partial_solve_wit_1_pure -> length_partial_solve_wit_1_aux.

Definition length_which_implies_wit_1 := 
forall (l2: (@list Z)) (p: Z) (PreH1 : (p <> 0)) ,
  (sll p l2 )
|--
  EX (p_next: Z)  (p_data: Z)  (l3: (@list Z)) ,
  “ (l2 = (cons (p_data) (l3))) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_entail_wit_1 := 
(
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll 0 l1 )
  **  (sll p_pre l2 )
) \/
(
forall (l: (@list Z)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((@nil Z)))) (l))) ”
  &&  emp
).

Definition reverse_entail_wit_1_split_goal_1 := 
forall (l: (@list Z)) ,
  (l = (app ((rev ((@nil Z)))) (l)))
.

Definition reverse_entail_wit_2 := 
(
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_next: Z) (v_data: Z) (l2_new: (@list Z)) (PreH1 : (l2_2 = (cons (v_data) (l2_new)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll v_next l2_new )
  **  (sll w l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v l1 )
  **  (sll v_next l2 )
) \/
(
forall (l: (@list Z)) (v: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_data: Z) (l2_new: (@list Z)) (PreH1 : (l2_2 = (cons (v_data) (l2_new)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (v_data) (l1_2))))) (l2_new))) ”
  &&  emp
).

Definition reverse_entail_wit_2_split_goal_1 := 
forall (l: (@list Z)) (v: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_data: Z) (l2_new: (@list Z)) (PreH1 : (l2_2 = (cons (v_data) (l2_new)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  (l = (app ((rev ((cons (v_data) (l1_2))))) (l2_new)))
.

Definition reverse_return_wit_1 := 
(
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll w l1 )
  **  (sll v l2 )
|--
  (sll w (rev (l)) )
) \/
(
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  “ (l1 = (rev (l))) ”
  &&  emp
).

Definition reverse_return_wit_1_split_goal_1 := 
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  “ (l1 = (rev (l))) ”
.

Definition reverse_return_wit_1_split_goal_spatial := 
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  TT && emp 
.

Definition reverse_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v <> 0)) ,
  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (v <> 0) ”
.

Definition reverse_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v <> 0)) ,
  (sll w l1 )
  **  (sll v l2 )
|--
  “ (v <> 0) ” 
  &&  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v <> 0) ”
  &&  (sll v l2 )
  **  (sll w l1 )
.

Definition reverse_partial_solve_wit_1 := reverse_partial_solve_wit_1_pure -> reverse_partial_solve_wit_1_aux.

Definition reverse_which_implies_wit_1 := 
forall (l2: (@list Z)) (v: Z) (PreH1 : (v <> 0)) ,
  (sll v l2 )
|--
  EX (v_next: Z)  (v_data: Z)  (l2_new: (@list Z)) ,
  “ (l2 = (cons (v_data) (l2_new))) ”
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> v_next)
  **  (sll v_next l2_new )
.

(*----- Function reverse_alter_style1 -----*)

Definition reverse_alter_style1_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_alter_style1_entail_wit_1 := 
(
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll 0 l1 )
  **  (sll p_pre l2 )
) \/
(
forall (l: (@list Z)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((@nil Z)))) (l))) ”
  &&  emp
).

Definition reverse_alter_style1_entail_wit_1_split_goal_1 := 
forall (l: (@list Z)) ,
  (l = (app ((rev ((@nil Z)))) (l)))
.

Definition reverse_alter_style1_entail_wit_2 := 
(
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (vn: Z) (x: Z) (xs: (@list Z)) (PreH1 : (l2_2 = (cons (x) (xs)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll vn xs )
  **  (sll w l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v l1 )
  **  (sll vn l2 )
) \/
(
forall (l: (@list Z)) (v: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (xs: (@list Z)) (PreH1 : (l2_2 = (cons (x) (xs)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (x) (l1_2))))) (xs))) ”
  &&  emp
).

Definition reverse_alter_style1_entail_wit_2_split_goal_1 := 
forall (l: (@list Z)) (v: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (xs: (@list Z)) (PreH1 : (l2_2 = (cons (x) (xs)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  (l = (app ((rev ((cons (x) (l1_2))))) (xs)))
.

Definition reverse_alter_style1_return_wit_1 := 
(
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll w l1 )
  **  (sll v l2 )
|--
  (sll w (rev (l)) )
) \/
(
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  “ (l1 = (rev (l))) ”
  &&  emp
).

Definition reverse_alter_style1_return_wit_1_split_goal_1 := 
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  “ (l1 = (rev (l))) ”
.

Definition reverse_alter_style1_return_wit_1_split_goal_spatial := 
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  TT && emp 
.

Definition reverse_alter_style1_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v <> 0)) ,
  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (v <> 0) ”
.

Definition reverse_alter_style1_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v <> 0)) ,
  (sll w l1 )
  **  (sll v l2 )
|--
  “ (v <> 0) ” 
  &&  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v <> 0) ”
  &&  (sll v l2 )
  **  (sll w l1 )
.

Definition reverse_alter_style1_partial_solve_wit_1 := reverse_alter_style1_partial_solve_wit_1_pure -> reverse_alter_style1_partial_solve_wit_1_aux.

Definition reverse_alter_style1_which_implies_wit_1 := 
forall (l2: (@list Z)) (v: Z) (PreH1 : (v <> 0)) ,
  (sll v l2 )
|--
  EX (vn: Z)  (x: Z)  (xs: (@list Z)) ,
  “ (l2 = (cons (x) (xs))) ”
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> vn)
  **  (sll vn xs )
.

(*----- Function reverse_alter_style2 -----*)

Definition reverse_alter_style2_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_alter_style2_entail_wit_1 := 
(
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll 0 l1 )
  **  (sll p_pre l2 )
) \/
(
forall (l: (@list Z)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((@nil Z)))) (l))) ”
  &&  emp
).

Definition reverse_alter_style2_entail_wit_1_split_goal_1 := 
forall (l: (@list Z)) ,
  (l = (app ((rev ((@nil Z)))) (l)))
.

Definition reverse_alter_style2_entail_wit_2 := 
(
forall (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_inv_next: Z) (x: Z) (xs: (@list Z)) (PreH1 : (l2_2 = (cons (x) (xs)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v_inv <> 0)) ,
  ((&((v_inv)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v_inv)  # "list" ->ₛ "next")) # Ptr  |-> w_inv)
  **  (sll v_inv_next xs )
  **  (sll w_inv l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v_inv l1 )
  **  (sll v_inv_next l2 )
) \/
(
forall (l: (@list Z)) (v_inv: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (xs: (@list Z)) (PreH1 : (l2_2 = (cons (x) (xs)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v_inv <> 0)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (x) (l1_2))))) (xs))) ”
  &&  emp
).

Definition reverse_alter_style2_entail_wit_2_split_goal_1 := 
forall (l: (@list Z)) (v_inv: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (xs: (@list Z)) (PreH1 : (l2_2 = (cons (x) (xs)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v_inv <> 0)) ,
  (l = (app ((rev ((cons (x) (l1_2))))) (xs)))
.

Definition reverse_alter_style2_return_wit_1 := 
(
forall (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v_inv = 0)) ,
  (sll w_inv l1 )
  **  (sll v_inv l2 )
|--
  (sll w_inv (rev (l)) )
) \/
(
forall (l: (@list Z)) (v_inv: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v_inv = 0)) ,
  (sll v_inv l2 )
|--
  “ (l1 = (rev (l))) ”
  &&  emp
).

Definition reverse_alter_style2_return_wit_1_split_goal_1 := 
forall (l: (@list Z)) (v_inv: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v_inv = 0)) ,
  (sll v_inv l2 )
|--
  “ (l1 = (rev (l))) ”
.

Definition reverse_alter_style2_return_wit_1_split_goal_spatial := 
forall (l: (@list Z)) (v_inv: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v_inv = 0)) ,
  (sll v_inv l2 )
|--
  TT && emp 
.

Definition reverse_alter_style2_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v_inv <> 0)) ,
  ((( &( "w" ) )) # Ptr  |-> w_inv)
  **  ((( &( "v" ) )) # Ptr  |-> v_inv)
  **  (sll w_inv l1 )
  **  (sll v_inv l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (v_inv <> 0) ”
.

Definition reverse_alter_style2_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v_inv <> 0)) ,
  (sll w_inv l1 )
  **  (sll v_inv l2 )
|--
  “ (v_inv <> 0) ” 
  &&  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v_inv <> 0) ”
  &&  (sll v_inv l2 )
  **  (sll w_inv l1 )
.

Definition reverse_alter_style2_partial_solve_wit_1 := reverse_alter_style2_partial_solve_wit_1_pure -> reverse_alter_style2_partial_solve_wit_1_aux.

Definition reverse_alter_style2_which_implies_wit_1 := 
forall (l2: (@list Z)) (v_inv: Z) (PreH1 : (v_inv <> 0)) ,
  (sll v_inv l2 )
|--
  EX (v_inv_next: Z)  (x: Z)  (xs: (@list Z)) ,
  “ (l2 = (cons (x) (xs))) ”
  &&  ((&((v_inv)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v_inv)  # "list" ->ₛ "next")) # Ptr  |-> v_inv_next)
  **  (sll v_inv_next xs )
.

(*----- Function reverse_alter_style3 -----*)

Definition reverse_alter_style3_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "v" ) )) # Ptr  |->_)
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_alter_style3_entail_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  (sll 0 (@nil Z) )
  **  (sll p_pre l )
.

Definition reverse_alter_style3_entail_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) ,
  (sll 0 (@nil Z) )
  **  (sll p_pre l )
|--
  “ (0 = 0) ” 
  &&  “ (p_pre = p_pre) ”
  &&  (sll 0 (@nil Z) )
  **  (sll p_pre l )
.

Definition reverse_alter_style3_entail_wit_3 := 
(
forall (p_pre: Z) (l: (@list Z)) (w: Z) (v: Z) (PreH1 : (w = 0)) (PreH2 : (v = p_pre)) ,
  (sll w (@nil Z) )
  **  (sll v l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll w l1 )
  **  (sll v l2 )
) \/
(
forall (p_pre: Z) (l: (@list Z)) (w: Z) (v: Z) (PreH1 : (w = 0)) (PreH2 : (w = 0)) (PreH3 : (v = p_pre)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((@nil Z)))) (l))) ”
  &&  emp
).

Definition reverse_alter_style3_entail_wit_3_split_goal_1 := 
forall (p_pre: Z) (l: (@list Z)) (w: Z) (v: Z) (PreH1 : (w = 0)) (PreH2 : (w = 0)) (PreH3 : (v = p_pre)) ,
  (l = (app ((rev ((@nil Z)))) (l)))
.

Definition reverse_alter_style3_entail_wit_4 := 
(
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_next: Z) (v_data: Z) (l2_new: (@list Z)) (PreH1 : (l2_2 = (cons (v_data) (l2_new)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll v_next l2_new )
  **  (sll w l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v l1 )
  **  (sll v_next l2 )
) \/
(
forall (l: (@list Z)) (v: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_data: Z) (l2_new: (@list Z)) (PreH1 : (l2_2 = (cons (v_data) (l2_new)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (v_data) (l1_2))))) (l2_new))) ”
  &&  emp
).

Definition reverse_alter_style3_entail_wit_4_split_goal_1 := 
forall (l: (@list Z)) (v: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_data: Z) (l2_new: (@list Z)) (PreH1 : (l2_2 = (cons (v_data) (l2_new)))) (PreH2 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH3 : (v <> 0)) ,
  (l = (app ((rev ((cons (v_data) (l1_2))))) (l2_new)))
.

Definition reverse_alter_style3_return_wit_1 := 
(
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll w l1 )
  **  (sll v l2 )
|--
  (sll w (rev (l)) )
) \/
(
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  “ (l1 = (rev (l))) ”
  &&  emp
).

Definition reverse_alter_style3_return_wit_1_split_goal_1 := 
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  “ (l1 = (rev (l))) ”
.

Definition reverse_alter_style3_return_wit_1_split_goal_spatial := 
forall (l: (@list Z)) (v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v = 0)) ,
  (sll v l2 )
|--
  TT && emp 
.

Definition reverse_alter_style3_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v <> 0)) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll v l2 )
|--
  “ (v <> 0) ”
.

Definition reverse_alter_style3_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app ((rev (l1))) (l2)))) (PreH2 : (v <> 0)) ,
  (sll w l1 )
  **  (sll v l2 )
|--
  “ (v <> 0) ” 
  &&  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v <> 0) ”
  &&  (sll v l2 )
  **  (sll w l1 )
.

Definition reverse_alter_style3_partial_solve_wit_1 := reverse_alter_style3_partial_solve_wit_1_pure -> reverse_alter_style3_partial_solve_wit_1_aux.

Definition reverse_alter_style3_which_implies_wit_1 := 
forall (l2: (@list Z)) (v: Z) (PreH1 : (v <> 0)) ,
  (sll v l2 )
|--
  EX (v_next: Z)  (v_data: Z)  (l2_new: (@list Z)) ,
  “ (l2 = (cons (v_data) (l2_new))) ”
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> v_next)
  **  (sll v_next l2_new )
.

(*----- Function append -----*)

Definition append_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_safety_wit_2 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH2 : (t <> 0)) (PreH3 : (t_next = u)) (PreH4 : (l1 = (cons (x_data) (l1n)))) (PreH5 : (x_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_next: Z) (x_data: Z) (l1n: (@list Z)) (PreH1 : (l1 = (cons (x_data) (l1n)))) (PreH2 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1n )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (t_data: Z)  (l1b: (@list Z)) ,
  “ ((app (l1a) ((cons (t_data) (l1b)))) = l1) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (t_next = x_next) ” 
  &&  “ (l1 = (cons (x_data) (l1n))) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre x_pre l1a )
  **  (sll x_next l1b )
  **  (sll y_pre l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (PreH1 : (l1 = (cons (x_data) (l1n)))) (PreH2 : (x_pre <> 0)) ,
  TT && emp 
|--
  “ ((app ((@nil Z)) ((cons (x_data) (l1n)))) = l1) ”
  &&  emp
).

Definition append_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (PreH1 : (l1 = (cons (x_data) (l1n)))) (PreH2 : (x_pre <> 0)) ,
  ((app ((@nil Z)) ((cons (x_data) (l1n)))) = l1)
.

Definition append_entail_wit_2 := 
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next_2: Z) (l1a_2: (@list Z)) (t_data_2: Z) (t: Z) (l1b_2: (@list Z)) (u_next: Z) (u_data: Z) (l1b_new: (@list Z)) (PreH1 : (l1b_2 = (cons (u_data) (l1b_new)))) (PreH2 : (u <> 0)) (PreH3 : ((app (l1a_2) ((cons (t_data_2) (l1b_2)))) = l1)) (PreH4 : (t <> 0)) (PreH5 : (t_next_2 = u)) (PreH6 : (l1 = (cons (x_data) (l1n)))) (PreH7 : (x_pre <> 0)) ,
  ((&((u)  # "list" ->ₛ "data")) # Int  |-> u_data)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> u_next)
  **  (sll u_next l1b_new )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x t l1a_2 )
  **  (sll y l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (t_data: Z)  (l1b: (@list Z)) ,
  “ ((app (l1a) ((cons (t_data) (l1b)))) = l1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (t_next = u_next) ” 
  &&  “ (l1 = (cons (x_data) (l1n))) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x u l1a )
  **  (sll u_next l1b )
  **  (sll y l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (x: Z) (u: Z) (t_next_2: Z) (l1a_2: (@list Z)) (t_data_2: Z) (t: Z) (l1b_2: (@list Z)) (u_data: Z) (l1b_new: (@list Z)) (PreH1 : (t_data_2 <= INT_MAX)) (PreH2 : (t_data_2 >= INT_MIN)) (PreH3 : (l1b_2 = (cons (u_data) (l1b_new)))) (PreH4 : (u <> 0)) (PreH5 : ((app (l1a_2) ((cons (t_data_2) (l1b_2)))) = l1)) (PreH6 : (t <> 0)) (PreH7 : (t_next_2 = u)) (PreH8 : (l1 = (cons (x_data) (l1n)))) (PreH9 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x t l1a_2 )
|--
  EX (l1a: (@list Z)) ,
  “ ((app (l1a) ((cons (u_data) (l1b_new)))) = l1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (l1 = (cons (x_data) (l1n))) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x u l1a )
).

Definition append_return_wit_1 := 
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : (u = 0)) (PreH2 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH3 : (t <> 0)) (PreH4 : (t_next = u)) (PreH5 : (l1 = (cons (x_data) (l1n)))) (PreH6 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
) \/
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : (t_data <= INT_MAX)) (PreH2 : (t_data >= INT_MIN)) (PreH3 : (u = 0)) (PreH4 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH5 : (t <> 0)) (PreH6 : (t_next = u)) (PreH7 : (l1 = (cons (x_data) (l1n)))) (PreH8 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
).

Definition append_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : (t_data <= INT_MAX)) (PreH2 : (t_data >= INT_MIN)) (PreH3 : (u = 0)) (PreH4 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH5 : (t <> 0)) (PreH6 : (t_next = u)) (PreH7 : (l1 = (cons (x_data) (l1n)))) (PreH8 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
.

Definition append_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  (sll y_pre (app (l1) (l2)) )
) \/
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
|--
  “ (l2 = (app (l1) (l2))) ”
  &&  emp
).

Definition append_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
|--
  “ (l2 = (app (l1) (l2))) ”
.

Definition append_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
|--
  TT && emp 
.

Definition append_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre <> 0)) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  “ (x_pre <> 0) ”
.

Definition append_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre <> 0)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
.

Definition append_partial_solve_wit_1 := append_partial_solve_wit_1_pure -> append_partial_solve_wit_1_aux.

Definition append_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : (u <> 0)) (PreH2 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH3 : (t <> 0)) (PreH4 : (t_next = u)) (PreH5 : (l1 = (cons (x_data) (l1n)))) (PreH6 : (x_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  “ (u <> 0) ”
.

Definition append_partial_solve_wit_2_aux := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : (u <> 0)) (PreH2 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH3 : (t <> 0)) (PreH4 : (t_next = u)) (PreH5 : (l1 = (cons (x_data) (l1n)))) (PreH6 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  (sll y l2 )
|--
  “ (u <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ ((app (l1a) ((cons (t_data) (l1b)))) = l1) ” 
  &&  “ (t <> 0) ” 
  &&  “ (t_next = u) ” 
  &&  “ (l1 = (cons (x_data) (l1n))) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sll u l1b )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll y l2 )
.

Definition append_partial_solve_wit_2 := append_partial_solve_wit_2_pure -> append_partial_solve_wit_2_aux.

Definition append_which_implies_wit_1 := 
forall (l1: (@list Z)) (x: Z) (PreH1 : (x <> 0)) ,
  (sll x l1 )
|--
  EX (x_next: Z)  (x_data: Z)  (l1n: (@list Z)) ,
  “ (l1 = (cons (x_data) (l1n))) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1n )
.

Definition append_which_implies_wit_2 := 
forall (l1b: (@list Z)) (u: Z) (PreH1 : (u <> 0)) ,
  (sll u l1b )
|--
  EX (u_next: Z)  (u_data: Z)  (l1b_new: (@list Z)) ,
  “ (l1b = (cons (u_data) (l1b_new))) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> u_data)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> u_next)
  **  (sll u_next l1b_new )
.

(*----- Function append_long -----*)

Definition append_long_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_long_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (l1 = (cons (a) (l1b)))) (PreH2 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
  **  ((( &( "u" ) )) # Ptr  |-> xn)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll y_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_long_safety_wit_3 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH2 : (t_next = u)) (PreH3 : (t <> 0)) (PreH4 : (xn <> 0)) (PreH5 : (l1 = (cons (a) (l1b)))) (PreH6 : (x_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_long_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (xn <> 0)) (PreH2 : (l1 = (cons (a) (l1b)))) (PreH3 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (b: Z)  (l1c: (@list Z)) ,
  “ ((app (l1a) ((cons (b) (l1c)))) = l1) ” 
  &&  “ (t_next = xn) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (xn <> 0) ” 
  &&  “ (l1 = (cons (a) (l1b))) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre x_pre l1a )
  **  (sll xn l1c )
  **  (sll y_pre l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (xn <> 0)) (PreH2 : (l1 = (cons (a) (l1b)))) (PreH3 : (x_pre <> 0)) ,
  TT && emp 
|--
  “ ((app ((@nil Z)) ((cons (a) (l1b)))) = l1) ”
  &&  emp
).

Definition append_long_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (xn <> 0)) (PreH2 : (l1 = (cons (a) (l1b)))) (PreH3 : (x_pre <> 0)) ,
  ((app ((@nil Z)) ((cons (a) (l1b)))) = l1)
.

Definition append_long_entail_wit_2 := 
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next_2: Z) (t: Z) (l1a_2: (@list Z)) (b_2: Z) (l1c_2: (@list Z)) (un: Z) (c: Z) (l1d: (@list Z)) (PreH1 : (l1c_2 = (cons (c) (l1d)))) (PreH2 : (u <> 0)) (PreH3 : ((app (l1a_2) ((cons (b_2) (l1c_2)))) = l1)) (PreH4 : (t_next_2 = u)) (PreH5 : (t <> 0)) (PreH6 : (xn <> 0)) (PreH7 : (l1 = (cons (a) (l1b)))) (PreH8 : (x_pre <> 0)) ,
  ((&((u)  # "list" ->ₛ "data")) # Int  |-> c)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> un)
  **  (sll un l1d )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x t l1a_2 )
  **  (sll y l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (b: Z)  (l1c: (@list Z)) ,
  “ ((app (l1a) ((cons (b) (l1c)))) = l1) ” 
  &&  “ (t_next = un) ” 
  &&  “ (u <> 0) ” 
  &&  “ (xn <> 0) ” 
  &&  “ (l1 = (cons (a) (l1b))) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x u l1a )
  **  (sll un l1c )
  **  (sll y l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (x: Z) (u: Z) (t_next_2: Z) (t: Z) (l1a_2: (@list Z)) (b_2: Z) (l1c_2: (@list Z)) (c: Z) (l1d: (@list Z)) (PreH1 : (b_2 <= INT_MAX)) (PreH2 : (b_2 >= INT_MIN)) (PreH3 : (l1c_2 = (cons (c) (l1d)))) (PreH4 : (u <> 0)) (PreH5 : ((app (l1a_2) ((cons (b_2) (l1c_2)))) = l1)) (PreH6 : (t_next_2 = u)) (PreH7 : (t <> 0)) (PreH8 : (xn <> 0)) (PreH9 : (l1 = (cons (a) (l1b)))) (PreH10 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x t l1a_2 )
|--
  EX (l1a: (@list Z)) ,
  “ ((app (l1a) ((cons (c) (l1d)))) = l1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (xn <> 0) ” 
  &&  “ (l1 = (cons (a) (l1b))) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x u l1a )
).

Definition append_long_return_wit_1 := 
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : (u = 0)) (PreH2 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH3 : (t_next = u)) (PreH4 : (t <> 0)) (PreH5 : (xn <> 0)) (PreH6 : (l1 = (cons (a) (l1b)))) (PreH7 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
) \/
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : (b <= INT_MAX)) (PreH2 : (b >= INT_MIN)) (PreH3 : (u = 0)) (PreH4 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH5 : (t_next = u)) (PreH6 : (t <> 0)) (PreH7 : (xn <> 0)) (PreH8 : (l1 = (cons (a) (l1b)))) (PreH9 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
).

Definition append_long_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : (b <= INT_MAX)) (PreH2 : (b >= INT_MIN)) (PreH3 : (u = 0)) (PreH4 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH5 : (t_next = u)) (PreH6 : (t <> 0)) (PreH7 : (xn <> 0)) (PreH8 : (l1 = (cons (a) (l1b)))) (PreH9 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
.

Definition append_long_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (xn = 0)) (PreH2 : (l1 = (cons (a) (l1b)))) (PreH3 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
|--
  (sll x_pre (app (l1) (l2)) )
) \/
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (xn = 0)) (PreH2 : (l1 = (cons (a) (l1b)))) (PreH3 : (x_pre <> 0)) ,
  (sll xn l1b )
|--
  “ ((app (l1) (l2)) = (cons (a) (l2))) ”
  &&  emp
).

Definition append_long_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (xn = 0)) (PreH2 : (l1 = (cons (a) (l1b)))) (PreH3 : (x_pre <> 0)) ,
  (sll xn l1b )
|--
  “ ((app (l1) (l2)) = (cons (a) (l2))) ”
.

Definition append_long_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (PreH1 : (xn = 0)) (PreH2 : (l1 = (cons (a) (l1b)))) (PreH3 : (x_pre <> 0)) ,
  (sll xn l1b )
|--
  TT && emp 
.

Definition append_long_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  (sll y_pre (app (l1) (l2)) )
) \/
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
|--
  “ (l2 = (app (l1) (l2))) ”
  &&  emp
).

Definition append_long_return_wit_3_split_goal_1 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
|--
  “ (l2 = (app (l1) (l2))) ”
.

Definition append_long_return_wit_3_split_goal_spatial := 
forall (x_pre: Z) (l1: (@list Z)) (PreH1 : (x_pre = 0)) ,
  (sll x_pre l1 )
|--
  TT && emp 
.

Definition append_long_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre <> 0)) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  “ (x_pre <> 0) ”
.

Definition append_long_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre <> 0)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
.

Definition append_long_partial_solve_wit_1 := append_long_partial_solve_wit_1_pure -> append_long_partial_solve_wit_1_aux.

Definition append_long_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : (u <> 0)) (PreH2 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH3 : (t_next = u)) (PreH4 : (t <> 0)) (PreH5 : (xn <> 0)) (PreH6 : (l1 = (cons (a) (l1b)))) (PreH7 : (x_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  “ (u <> 0) ”
.

Definition append_long_partial_solve_wit_2_aux := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : (u <> 0)) (PreH2 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH3 : (t_next = u)) (PreH4 : (t <> 0)) (PreH5 : (xn <> 0)) (PreH6 : (l1 = (cons (a) (l1b)))) (PreH7 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  (sll y l2 )
|--
  “ (u <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ ((app (l1a) ((cons (b) (l1c)))) = l1) ” 
  &&  “ (t_next = u) ” 
  &&  “ (t <> 0) ” 
  &&  “ (xn <> 0) ” 
  &&  “ (l1 = (cons (a) (l1b))) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sll u l1c )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll y l2 )
.

Definition append_long_partial_solve_wit_2 := append_long_partial_solve_wit_2_pure -> append_long_partial_solve_wit_2_aux.

Definition append_long_which_implies_wit_1 := 
forall (l1: (@list Z)) (x: Z) (PreH1 : (x <> 0)) ,
  (sll x l1 )
|--
  EX (xn: Z)  (a: Z)  (l1b: (@list Z)) ,
  “ (l1 = (cons (a) (l1b))) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
.

Definition append_long_which_implies_wit_2 := 
forall (l1cd: (@list Z)) (u: Z) (PreH1 : (u <> 0)) ,
  (sll u l1cd )
|--
  EX (un: Z)  (c: Z)  (l1d: (@list Z)) ,
  “ (l1cd = (cons (c) (l1d))) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> c)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> un)
  **  (sll un l1d )
.

(*----- Function append_2p -----*)

Definition append_2p_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  EX (l1a: (@list Z))  (l1b: (@list Z)) ,
  “ ((app (l1a) (l1b)) = l1) ”
  &&  (sllbseg ( &( "x" ) ) ( &( "x" ) ) l1a )
  **  (sll x_pre l1b )
  **  (sll y_pre l2 )
) \/
(
forall (l1: (@list Z)) ,
  TT && emp 
|--
  EX (l1a: (@list Z)) ,
  “ ((app (l1a) (l1)) = l1) ”
  &&  (sllbseg ( &( "x" ) ) ( &( "x" ) ) l1a )
).

Definition append_2p_entail_wit_2 := 
(
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v_2: Z) (pt: Z) (l1a_2: (@list Z)) (l1b_2: (@list Z)) (PreH1 : ((app (l1a_2) (l1b_2)) = l1)) (PreH2 : (pt_v_2 <> 0)) ,
  (sllbseg ( &( "x" ) ) pt l1a_2 )
  **  ((pt) # Ptr  |-> pt_v_2)
  **  (sll pt_v_2 l1b_2 )
  **  (sll y l2 )
|--
  EX (pt_v: Z)  (l1a: (@list Z))  (l1b: (@list Z)) ,
  “ ((app (l1a) (l1b)) = l1) ”
  &&  (sllbseg ( &( "x" ) ) &((pt_v_2)  # "list" ->ₛ "next") l1a )
  **  ((&((pt_v_2)  # "list" ->ₛ "next")) # Ptr  |-> pt_v)
  **  (sll pt_v l1b )
  **  (sll y l2 )
) \/
(
forall (l1: (@list Z)) (pt_v_2: Z) (pt: Z) (l1a_2: (@list Z)) (l1b_2: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (l1b_2 = (cons (x) (l0)))) (PreH4 : ((app (l1a_2) (l1b_2)) = l1)) (PreH5 : (pt_v_2 <> 0)) ,
  ((&((pt_v_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllbseg ( &( "x" ) ) pt l1a_2 )
  **  ((pt) # Ptr  |-> pt_v_2)
|--
  EX (l1a: (@list Z)) ,
  “ ((app (l1a) (l0)) = l1) ”
  &&  (sllbseg ( &( "x" ) ) &((pt_v_2)  # "list" ->ₛ "next") l1a )
).

Definition append_2p_return_wit_1 := 
(
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (l1a: (@list Z)) (l1b: (@list Z)) (pres_v: Z) (PreH1 : ((app (l1a) (l1b)) = l1)) (PreH2 : (pt_v = 0)) ,
  (sllseg pres_v y l1a )
  **  (sll pt_v l1b )
  **  (sll y l2 )
|--
  (sll pres_v (app (l1) (l2)) )
) \/
(
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (l1a: (@list Z)) (l1b: (@list Z)) (pres_v: Z) (PreH1 : ((app (l1a) (l1b)) = l1)) (PreH2 : (pt_v = 0)) ,
  (sllseg pres_v y l1a )
  **  (sll pt_v l1b )
  **  (sll y l2 )
|--
  (sll pres_v (app (l1) (l2)) )
).

Definition append_2p_return_wit_1_split_goal_spatial := 
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (l1a: (@list Z)) (l1b: (@list Z)) (pres_v: Z) (PreH1 : ((app (l1a) (l1b)) = l1)) (PreH2 : (pt_v = 0)) ,
  (sllseg pres_v y l1a )
  **  (sll pt_v l1b )
  **  (sll y l2 )
|--
  (sll pres_v (app (l1) (l2)) )
.

Definition append_2p_partial_solve_wit_1_pure := 
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (pt: Z) (l1a: (@list Z)) (l1b: (@list Z)) (PreH1 : ((app (l1a) (l1b)) = l1)) (PreH2 : (pt_v = 0)) ,
  ((( &( "pres" ) )) # Ptr  |-> ( &( "x" ) ))
  **  ((( &( "pt" ) )) # Ptr  |-> pt)
  **  (sllbseg ( &( "x" ) ) pt l1a )
  **  ((pt) # Ptr  |-> y)
  **  (sll pt_v l1b )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  “ (y = y) ”
.

Definition append_2p_partial_solve_wit_1_aux := 
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (pt: Z) (l1a: (@list Z)) (l1b: (@list Z)) (PreH1 : ((app (l1a) (l1b)) = l1)) (PreH2 : (pt_v = 0)) ,
  (sllbseg ( &( "x" ) ) pt l1a )
  **  ((pt) # Ptr  |-> y)
  **  (sll pt_v l1b )
  **  (sll y l2 )
|--
  “ (y = y) ” 
  &&  “ ((app (l1a) (l1b)) = l1) ” 
  &&  “ (pt_v = 0) ”
  &&  ((pt) # Ptr  |-> y)
  **  (sllbseg ( &( "x" ) ) pt l1a )
  **  (sll pt_v l1b )
  **  (sll y l2 )
.

Definition append_2p_partial_solve_wit_1 := append_2p_partial_solve_wit_1_pure -> append_2p_partial_solve_wit_1_aux.

Definition append_2p_which_implies_wit_1 := 
(
forall (l1a: (@list Z)) (pt: Z) (pt_v: Z) (y: Z) (pres: Z) (PreH1 : (pt_v = y)) ,
  ((pt) # Ptr  |-> pt_v)
  **  (sllbseg pres pt l1a )
|--
  EX (pres_v: Z) ,
  ((pres) # Ptr  |-> pres_v)
  **  (sllseg pres_v y l1a )
) \/
(
forall (l1a: (@list Z)) (pt: Z) (pt_v: Z) (y: Z) (pres: Z) (PreH1 : (pt_v = y)) ,
  ((pt) # Ptr  |-> pt_v)
  **  (sllbseg pres pt l1a )
|--
  EX (pres_v: Z) ,
  ((pres) # Ptr  |-> pres_v)
  **  (sllseg pres_v y l1a )
).

Module Type VC_Correct.

Include sll_Strategy_Correct.

Axiom proof_of_length_safety_wit_1 : length_safety_wit_1.
Axiom proof_of_length_safety_wit_2 : length_safety_wit_2.
Axiom proof_of_length_entail_wit_1 : length_entail_wit_1.
Axiom proof_of_length_entail_wit_2 : length_entail_wit_2.
Axiom proof_of_length_return_wit_1 : length_return_wit_1.
Axiom proof_of_length_partial_solve_wit_1_pure : length_partial_solve_wit_1_pure.
Axiom proof_of_length_partial_solve_wit_1 : length_partial_solve_wit_1.
Axiom proof_of_length_which_implies_wit_1 : length_which_implies_wit_1.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1_pure : reverse_partial_solve_wit_1_pure.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_reverse_which_implies_wit_1 : reverse_which_implies_wit_1.
Axiom proof_of_reverse_alter_style1_safety_wit_1 : reverse_alter_style1_safety_wit_1.
Axiom proof_of_reverse_alter_style1_entail_wit_1 : reverse_alter_style1_entail_wit_1.
Axiom proof_of_reverse_alter_style1_entail_wit_2 : reverse_alter_style1_entail_wit_2.
Axiom proof_of_reverse_alter_style1_return_wit_1 : reverse_alter_style1_return_wit_1.
Axiom proof_of_reverse_alter_style1_partial_solve_wit_1_pure : reverse_alter_style1_partial_solve_wit_1_pure.
Axiom proof_of_reverse_alter_style1_partial_solve_wit_1 : reverse_alter_style1_partial_solve_wit_1.
Axiom proof_of_reverse_alter_style1_which_implies_wit_1 : reverse_alter_style1_which_implies_wit_1.
Axiom proof_of_reverse_alter_style2_safety_wit_1 : reverse_alter_style2_safety_wit_1.
Axiom proof_of_reverse_alter_style2_entail_wit_1 : reverse_alter_style2_entail_wit_1.
Axiom proof_of_reverse_alter_style2_entail_wit_2 : reverse_alter_style2_entail_wit_2.
Axiom proof_of_reverse_alter_style2_return_wit_1 : reverse_alter_style2_return_wit_1.
Axiom proof_of_reverse_alter_style2_partial_solve_wit_1_pure : reverse_alter_style2_partial_solve_wit_1_pure.
Axiom proof_of_reverse_alter_style2_partial_solve_wit_1 : reverse_alter_style2_partial_solve_wit_1.
Axiom proof_of_reverse_alter_style2_which_implies_wit_1 : reverse_alter_style2_which_implies_wit_1.
Axiom proof_of_reverse_alter_style3_safety_wit_1 : reverse_alter_style3_safety_wit_1.
Axiom proof_of_reverse_alter_style3_entail_wit_1 : reverse_alter_style3_entail_wit_1.
Axiom proof_of_reverse_alter_style3_entail_wit_2 : reverse_alter_style3_entail_wit_2.
Axiom proof_of_reverse_alter_style3_entail_wit_3 : reverse_alter_style3_entail_wit_3.
Axiom proof_of_reverse_alter_style3_entail_wit_4 : reverse_alter_style3_entail_wit_4.
Axiom proof_of_reverse_alter_style3_return_wit_1 : reverse_alter_style3_return_wit_1.
Axiom proof_of_reverse_alter_style3_partial_solve_wit_1_pure : reverse_alter_style3_partial_solve_wit_1_pure.
Axiom proof_of_reverse_alter_style3_partial_solve_wit_1 : reverse_alter_style3_partial_solve_wit_1.
Axiom proof_of_reverse_alter_style3_which_implies_wit_1 : reverse_alter_style3_which_implies_wit_1.
Axiom proof_of_append_safety_wit_1 : append_safety_wit_1.
Axiom proof_of_append_safety_wit_2 : append_safety_wit_2.
Axiom proof_of_append_entail_wit_1 : append_entail_wit_1.
Axiom proof_of_append_entail_wit_2 : append_entail_wit_2.
Axiom proof_of_append_return_wit_1 : append_return_wit_1.
Axiom proof_of_append_return_wit_2 : append_return_wit_2.
Axiom proof_of_append_partial_solve_wit_1_pure : append_partial_solve_wit_1_pure.
Axiom proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Axiom proof_of_append_partial_solve_wit_2_pure : append_partial_solve_wit_2_pure.
Axiom proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Axiom proof_of_append_which_implies_wit_1 : append_which_implies_wit_1.
Axiom proof_of_append_which_implies_wit_2 : append_which_implies_wit_2.
Axiom proof_of_append_long_safety_wit_1 : append_long_safety_wit_1.
Axiom proof_of_append_long_safety_wit_2 : append_long_safety_wit_2.
Axiom proof_of_append_long_safety_wit_3 : append_long_safety_wit_3.
Axiom proof_of_append_long_entail_wit_1 : append_long_entail_wit_1.
Axiom proof_of_append_long_entail_wit_2 : append_long_entail_wit_2.
Axiom proof_of_append_long_return_wit_1 : append_long_return_wit_1.
Axiom proof_of_append_long_return_wit_2 : append_long_return_wit_2.
Axiom proof_of_append_long_return_wit_3 : append_long_return_wit_3.
Axiom proof_of_append_long_partial_solve_wit_1_pure : append_long_partial_solve_wit_1_pure.
Axiom proof_of_append_long_partial_solve_wit_1 : append_long_partial_solve_wit_1.
Axiom proof_of_append_long_partial_solve_wit_2_pure : append_long_partial_solve_wit_2_pure.
Axiom proof_of_append_long_partial_solve_wit_2 : append_long_partial_solve_wit_2.
Axiom proof_of_append_long_which_implies_wit_1 : append_long_which_implies_wit_1.
Axiom proof_of_append_long_which_implies_wit_2 : append_long_which_implies_wit_2.
Axiom proof_of_append_2p_entail_wit_1 : append_2p_entail_wit_1.
Axiom proof_of_append_2p_entail_wit_2 : append_2p_entail_wit_2.
Axiom proof_of_append_2p_return_wit_1 : append_2p_return_wit_1.
Axiom proof_of_append_2p_partial_solve_wit_1_pure : append_2p_partial_solve_wit_1_pure.
Axiom proof_of_append_2p_partial_solve_wit_1 : append_2p_partial_solve_wit_1.
Axiom proof_of_append_2p_which_implies_wit_1 : append_2p_which_implies_wit_1.

End VC_Correct.
