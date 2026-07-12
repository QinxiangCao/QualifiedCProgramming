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
Require Import SimpleC.EE.QCP_demos_human.sll_insert_sort_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_proof.

(*----- Function insertion -----*)

Definition insertion_safety_wit_1 := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (strict_upperbound a l1 )) (PreH3 : (node_pre <> 0)) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insertion_entail_wit_1 := 
(
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (PreH1 : (node_pre <> 0)) ,
  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p_pre l )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) ( &( "res" ) ) l1 )
  **  (sll p_pre l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
) \/
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (PreH1 : (node_pre <> 0)) ,
  TT && emp 
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  (sllbseg ( &( "res" ) ) ( &( "res" ) ) l1 )
).

Definition insertion_entail_wit_2 := 
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v_2: Z) (p2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (p2_v_next: Z) (p2_v_data: Z) (l3: (@list Z)) (PreH1 : ((cons (x) (l0)) = (cons (p2_v_data) (l3)))) (PreH2 : (x < a)) (PreH3 : (l2_2 = (cons (x) (l0)))) (PreH4 : (p2_v_2 <> 0)) (PreH5 : (l = (app (l1_2) (l2_2)))) (PreH6 : (strict_upperbound a l1_2 )) (PreH7 : (node_pre <> 0)) ,
  ((p2) # Ptr  |-> p2_v_2)
  **  ((&((p2_v_2)  # "list" ->ₛ "data")) # Int  |-> p2_v_data)
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p2_v_next)
  **  (sll p2_v_next l3 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (p2_v: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) &((p2_v_2)  # "list" ->ₛ "next") l1 )
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
) \/
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v_2: Z) (p2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (p2_v_data: Z) (l3: (@list Z)) (PreH1 : (p2_v_data <= INT_MAX)) (PreH2 : (p2_v_data >= INT_MIN)) (PreH3 : ((cons (x) (l0)) = (cons (p2_v_data) (l3)))) (PreH4 : (x < a)) (PreH5 : (l2_2 = (cons (x) (l0)))) (PreH6 : (p2_v_2 <> 0)) (PreH7 : (l = (app (l1_2) (l2_2)))) (PreH8 : (strict_upperbound a l1_2 )) (PreH9 : (node_pre <> 0)) ,
  ((p2) # Ptr  |-> p2_v_2)
  **  ((&((p2_v_2)  # "list" ->ₛ "data")) # Int  |-> p2_v_data)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l3))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  (sllbseg ( &( "res" ) ) &((p2_v_2)  # "list" ->ₛ "next") l1 )
).

Definition insertion_return_wit_1 := 
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (res: Z) (PreH1 : (p2_v = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (strict_upperbound a l1 )) (PreH4 : (node_pre <> 0)) ,
  (sllseg res node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  EX (l0: (@list Z)) ,
  “ (l0 = (insert (a) (l))) ”
  &&  (sll res l0 )
) \/
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (res: Z) (PreH1 : (a <= INT_MAX)) (PreH2 : (a >= INT_MIN)) (PreH3 : (p2_v = 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (strict_upperbound a l1 )) (PreH6 : (node_pre <> 0)) ,
  (sllseg res node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  (sll res (insert (a) (l)) )
).

Definition insertion_return_wit_1_split_goal_spatial := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (res: Z) (PreH1 : (a <= INT_MAX)) (PreH2 : (a >= INT_MIN)) (PreH3 : (p2_v = 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (strict_upperbound a l1 )) (PreH6 : (node_pre <> 0)) ,
  (sllseg res node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  (sll res (insert (a) (l)) )
.

Definition insertion_return_wit_2 := 
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0_2: (@list Z)) (y: Z) (res: Z) (PreH1 : (x >= a)) (PreH2 : (l2 = (cons (x) (l0_2)))) (PreH3 : (p2_v <> 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (strict_upperbound a l1 )) (PreH6 : (node_pre <> 0)) ,
  (sllseg res node_pre l1 )
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0_2 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  EX (l0: (@list Z)) ,
  “ (l0 = (insert (a) (l))) ”
  &&  (sll res l0 )
) \/
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0_2: (@list Z)) (y: Z) (res: Z) (PreH1 : (a <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (a >= INT_MIN)) (PreH4 : (x >= INT_MIN)) (PreH5 : (x >= a)) (PreH6 : (l2 = (cons (x) (l0_2)))) (PreH7 : (p2_v <> 0)) (PreH8 : (l = (app (l1) (l2)))) (PreH9 : (strict_upperbound a l1 )) (PreH10 : (node_pre <> 0)) ,
  (sllseg res node_pre l1 )
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0_2 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  (sll res (insert (a) (l)) )
).

Definition insertion_return_wit_2_split_goal_spatial := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0_2: (@list Z)) (y: Z) (res: Z) (PreH1 : (a <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (a >= INT_MIN)) (PreH4 : (x >= INT_MIN)) (PreH5 : (x >= a)) (PreH6 : (l2 = (cons (x) (l0_2)))) (PreH7 : (p2_v <> 0)) (PreH8 : (l = (app (l1) (l2)))) (PreH9 : (strict_upperbound a l1 )) (PreH10 : (node_pre <> 0)) ,
  (sllseg res node_pre l1 )
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0_2 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  (sll res (insert (a) (l)) )
.

Definition insertion_partial_solve_wit_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p2_v <> 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (strict_upperbound a l1 )) (PreH4 : (node_pre <> 0)) ,
  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (p2_v <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_partial_solve_wit_2_pure := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (x < a)) (PreH2 : (l2 = (cons (x) (l0)))) (PreH3 : (p2_v <> 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (strict_upperbound a l1 )) (PreH6 : (node_pre <> 0)) ,
  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (p2_v <> 0) ”
.

Definition insertion_partial_solve_wit_2_aux := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (x < a)) (PreH2 : (l2 = (cons (x) (l0)))) (PreH3 : (p2_v <> 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (strict_upperbound a l1 )) (PreH6 : (node_pre <> 0)) ,
  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  “ (p2_v <> 0) ” 
  &&  “ (x < a) ” 
  &&  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (p2_v <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v (cons (x) (l0)) )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_partial_solve_wit_2 := insertion_partial_solve_wit_2_pure -> insertion_partial_solve_wit_2_aux.

Definition insertion_partial_solve_wit_3_pure := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (x >= a)) (PreH2 : (l2 = (cons (x) (l0)))) (PreH3 : (p2_v <> 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (strict_upperbound a l1 )) (PreH6 : (node_pre <> 0)) ,
  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (node_pre = node_pre) ”
.

Definition insertion_partial_solve_wit_3_aux := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (x >= a)) (PreH2 : (l2 = (cons (x) (l0)))) (PreH3 : (p2_v <> 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (strict_upperbound a l1 )) (PreH6 : (node_pre <> 0)) ,
  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  “ (node_pre = node_pre) ” 
  &&  “ (x >= a) ” 
  &&  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (p2_v <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  ((p2) # Ptr  |-> node_pre)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
.

Definition insertion_partial_solve_wit_3 := insertion_partial_solve_wit_3_pure -> insertion_partial_solve_wit_3_aux.

Definition insertion_partial_solve_wit_4_pure := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p2_v = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (strict_upperbound a l1 )) (PreH4 : (node_pre <> 0)) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (node_pre = node_pre) ”
.

Definition insertion_partial_solve_wit_4_aux := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p2_v = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (strict_upperbound a l1 )) (PreH4 : (node_pre <> 0)) ,
  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  “ (node_pre = node_pre) ” 
  &&  “ (p2_v = 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ” 
  &&  “ (node_pre <> 0) ”
  &&  ((p2) # Ptr  |-> node_pre)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
.

Definition insertion_partial_solve_wit_4 := insertion_partial_solve_wit_4_pure -> insertion_partial_solve_wit_4_aux.

Definition insertion_which_implies_wit_1 := 
forall (l2: (@list Z)) (p2: Z) (p2_v: Z) (PreH1 : (p2_v <> 0)) ,
  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
|--
  EX (p2_v_next: Z)  (p2_v_data: Z)  (l3: (@list Z)) ,
  “ (l2 = (cons (p2_v_data) (l3))) ”
  &&  ((p2) # Ptr  |-> p2_v)
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> p2_v_data)
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> p2_v_next)
  **  (sll p2_v_next l3 )
.

Definition insertion_which_implies_wit_2 := 
(
forall (l1: (@list Z)) (p2: Z) (p2_v: Z) (node: Z) (PreH1 : (p2_v = node)) ,
  ((p2) # Ptr  |-> p2_v)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
|--
  EX (res: Z) ,
  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sllseg res node l1 )
) \/
(
forall (l1: (@list Z)) (p2: Z) (p2_v: Z) (node: Z) (PreH1 : (p2_v = node)) ,
  ((p2) # Ptr  |-> p2_v)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
|--
  EX (res: Z) ,
  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sllseg res node l1 )
).

(*----- Function insertion_sort -----*)

Definition insertion_sort_safety_wit_1 := 
forall (x_pre: Z) (l: (@list Z)) ,
  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insertion_sort_safety_wit_2 := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (Permutation l1 l0 )) (PreH3 : (increasing l0 )) ,
  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l2 )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insertion_sort_entail_wit_1 := 
(
forall (x_pre: Z) (l: (@list Z)) ,
  (sll x_pre l )
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (sll 0 l0 )
  **  (sll x_pre l2 )
) \/
(
forall (l: (@list Z)) ,
  TT && emp 
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l))) ” 
  &&  “ (Permutation l1 (@nil Z) ) ” 
  &&  “ (increasing (@nil Z) ) ”
  &&  emp
).

Definition insertion_sort_entail_wit_2 := 
(
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (l0_3: (@list Z)) (retval: Z) (PreH1 : (l0_3 = (insert (p_data) (l0_2)))) (PreH2 : (l2_2 = (cons (p_data) (l3)))) (PreH3 : (p <> 0)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (Permutation l1_2 l0_2 )) (PreH6 : (increasing l0_2 )) ,
  (sll retval l0_3 )
  **  (sll p_next l3 )
  **  ((( &( "q" ) )) # Ptr  |-> p_next)
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (sll retval l0 )
  **  (sll p_next l2 )
  **  ((( &( "q" ) )) # Ptr  |->_)
) \/
(
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_data: Z) (l3: (@list Z)) (l0_3: (@list Z)) (PreH1 : (l0_3 = (insert (p_data) (l0_2)))) (PreH2 : (l2_2 = (cons (p_data) (l3)))) (PreH3 : (p <> 0)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (Permutation l1_2 l0_2 )) (PreH6 : (increasing l0_2 )) ,
  TT && emp 
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l3))) ” 
  &&  “ (Permutation l1 l0_3 ) ” 
  &&  “ (increasing l0_3 ) ”
  &&  emp
).

Definition insertion_sort_return_wit_1 := 
(
forall (l: (@list Z)) (p: Z) (res: Z) (l0_2: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (Permutation l1 l0_2 )) (PreH4 : (increasing l0_2 )) ,
  (sll res l0_2 )
  **  (sll p l2 )
|--
  EX (l0: (@list Z)) ,
  “ (Permutation l l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (sll res l0 )
) \/
(
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (Permutation l1 l0_2 )) (PreH4 : (increasing l0_2 )) ,
  (sll p l2 )
|--
  “ (Permutation l l0_2 ) ”
  &&  emp
).

Definition insertion_sort_return_wit_1_split_goal_1 := 
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (Permutation l1 l0_2 )) (PreH4 : (increasing l0_2 )) ,
  (sll p l2 )
|--
  “ (Permutation l l0_2 ) ”
.

Definition insertion_sort_return_wit_1_split_goal_spatial := 
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (Permutation l1 l0_2 )) (PreH4 : (increasing l0_2 )) ,
  (sll p l2 )
|--
  TT && emp 
.

Definition insertion_sort_partial_solve_wit_1_pure := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p <> 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (Permutation l1 l0 )) (PreH4 : (increasing l0 )) ,
  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l2 )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (p <> 0) ”
.

Definition insertion_sort_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p <> 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (Permutation l1 l0 )) (PreH4 : (increasing l0 )) ,
  (sll res l0 )
  **  (sll p l2 )
|--
  “ (p <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (sll p l2 )
  **  (sll res l0 )
.

Definition insertion_sort_partial_solve_wit_1 := insertion_sort_partial_solve_wit_1_pure -> insertion_sort_partial_solve_wit_1_aux.

Definition insertion_sort_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (p <> 0)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (Permutation l1 l0 )) (PreH5 : (increasing l0 )) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "q" ) )) # Ptr  |-> p_next)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (p <> 0) ”
.

Definition insertion_sort_partial_solve_wit_2_aux := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (PreH1 : (l2 = (cons (p_data) (l3)))) (PreH2 : (p <> 0)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (Permutation l1 l0 )) (PreH5 : (increasing l0 )) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sll res l0 )
|--
  “ (p <> 0) ” 
  &&  “ (l2 = (cons (p_data) (l3))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  (sll res l0 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sll p_next l3 )
.

Definition insertion_sort_partial_solve_wit_2 := insertion_sort_partial_solve_wit_2_pure -> insertion_sort_partial_solve_wit_2_aux.

Definition insertion_sort_which_implies_wit_1 := 
forall (l2: (@list Z)) (p: Z) (PreH1 : (p <> 0)) ,
  (sll p l2 )
|--
  EX (p_next: Z)  (p_data: Z)  (l3: (@list Z)) ,
  “ (l2 = (cons (p_data) (l3))) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
.

Module Type VC_Correct.

Include sll_Strategy_Correct.

Axiom proof_of_insertion_safety_wit_1 : insertion_safety_wit_1.
Axiom proof_of_insertion_entail_wit_1 : insertion_entail_wit_1.
Axiom proof_of_insertion_entail_wit_2 : insertion_entail_wit_2.
Axiom proof_of_insertion_return_wit_1 : insertion_return_wit_1.
Axiom proof_of_insertion_return_wit_2 : insertion_return_wit_2.
Axiom proof_of_insertion_partial_solve_wit_1 : insertion_partial_solve_wit_1.
Axiom proof_of_insertion_partial_solve_wit_2_pure : insertion_partial_solve_wit_2_pure.
Axiom proof_of_insertion_partial_solve_wit_2 : insertion_partial_solve_wit_2.
Axiom proof_of_insertion_partial_solve_wit_3_pure : insertion_partial_solve_wit_3_pure.
Axiom proof_of_insertion_partial_solve_wit_3 : insertion_partial_solve_wit_3.
Axiom proof_of_insertion_partial_solve_wit_4_pure : insertion_partial_solve_wit_4_pure.
Axiom proof_of_insertion_partial_solve_wit_4 : insertion_partial_solve_wit_4.
Axiom proof_of_insertion_which_implies_wit_1 : insertion_which_implies_wit_1.
Axiom proof_of_insertion_which_implies_wit_2 : insertion_which_implies_wit_2.
Axiom proof_of_insertion_sort_safety_wit_1 : insertion_sort_safety_wit_1.
Axiom proof_of_insertion_sort_safety_wit_2 : insertion_sort_safety_wit_2.
Axiom proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Axiom proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Axiom proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_1_pure : insertion_sort_partial_solve_wit_1_pure.
Axiom proof_of_insertion_sort_partial_solve_wit_1 : insertion_sort_partial_solve_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_2_pure : insertion_sort_partial_solve_wit_2_pure.
Axiom proof_of_insertion_sort_partial_solve_wit_2 : insertion_sort_partial_solve_wit_2.
Axiom proof_of_insertion_sort_which_implies_wit_1 : insertion_sort_which_implies_wit_1.

End VC_Correct.
