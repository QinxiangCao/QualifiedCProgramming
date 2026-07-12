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
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import SimpleC.EE.QCP_demos_LLM.sll_insert_sort_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function insertion -----*)

Definition insertion_safety_wit_1 := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (node_pre <> 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (strict_upperbound a l1 )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
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
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ”
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
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) (l))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  (sllbseg ( &( "res" ) ) ( &( "res" ) ) l1 )
).

Definition insertion_entail_wit_2 := 
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v_2: Z) (p2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (x < a)) (PreH2 : (l2_2 = (cons (x) (l0)))) (PreH3 : (p2_v_2 <> 0)) (PreH4 : (node_pre <> 0)) (PreH5 : (l = (app (l1_2) (l2_2)))) (PreH6 : (strict_upperbound a l1_2 )) ,
  ((&((p2_v_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((p2) # Ptr  |-> p2_v_2)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (p2_v: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) &((p2_v_2)  # "list" ->ₛ "next") l1 )
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
) \/
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v_2: Z) (p2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (x < a)) (PreH4 : (l2_2 = (cons (x) (l0)))) (PreH5 : (p2_v_2 <> 0)) (PreH6 : (node_pre <> 0)) (PreH7 : (l = (app (l1_2) (l2_2)))) (PreH8 : (strict_upperbound a l1_2 )) ,
  ((&((p2_v_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((p2) # Ptr  |-> p2_v_2)
|--
  EX (l1: (@list Z)) ,
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) (l0))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  (sllbseg ( &( "res" ) ) &((p2_v_2)  # "list" ->ₛ "next") l1 )
).

Definition insertion_entail_wit_3_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1_3: (@list Z)) (l2: (@list Z)) (x_2: Z) (l0_2: (@list Z)) (y: Z) (PreH1 : (x_2 >= a)) (PreH2 : (l2 = (cons (x_2) (l0_2)))) (PreH3 : (p2_v <> 0)) (PreH4 : (node_pre <> 0)) (PreH5 : (l = (app (l1_3) (l2)))) (PreH6 : (strict_upperbound a l1_3 )) ,
  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sll y l0_2 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  (EX (l1: (@list Z)) ,
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) ((@nil Z)))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> 0)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
  ||
  (EX (unext: Z)  (l1_2: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  “ (node_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x >= a) ” 
  &&  “ (l = (app (l1_2) ((cons (x) (l0))))) ” 
  &&  “ (strict_upperbound a l1_2 ) ”
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((p2) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
.

Definition insertion_entail_wit_3_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1_3: (@list Z)) (l2: (@list Z)) (PreH1 : (p2_v = 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (l = (app (l1_3) (l2)))) (PreH4 : (strict_upperbound a l1_3 )) ,
  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  (EX (l1: (@list Z)) ,
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) ((@nil Z)))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> 0)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
  ||
  (EX (unext: Z)  (l1_2: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  “ (node_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x >= a) ” 
  &&  “ (l = (app (l1_2) ((cons (x) (l0))))) ” 
  &&  “ (strict_upperbound a l1_2 ) ”
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((p2) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
.

Definition insertion_entail_wit_4_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (l1_3: (@list Z)) (x_2: Z) (l0_2: (@list Z)) (u_2: Z) (unext_2: Z) (p2: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (u_2 <> 0)) (PreH3 : (x_2 >= a)) (PreH4 : (l = (app (l1_3) ((cons (x_2) (l0_2)))))) (PreH5 : (strict_upperbound a l1_3 )) ,
  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((u_2)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((u_2)  # "list" ->ₛ "next")) # Ptr  |-> unext_2)
  **  (sll unext_2 l0_2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u_2)
|--
  (EX (resv: Z)  (l1: (@list Z)) ,
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) ((@nil Z)))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  ((( &( "res" ) )) # Ptr  |-> resv)
  **  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0))
  ||
  (EX (unext: Z)  (resv_2: Z)  (l1_2: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  “ (node_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x >= a) ” 
  &&  “ (l = (app (l1_2) ((cons (x) (l0))))) ” 
  &&  “ (strict_upperbound a l1_2 ) ”
  &&  ((( &( "res" ) )) # Ptr  |-> resv_2)
  **  (sllseg resv_2 node_pre l1_2 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 ))
.

Definition insertion_entail_wit_4_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (l1_3: (@list Z)) (p2: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (l = (app (l1_3) ((@nil Z))))) (PreH3 : (strict_upperbound a l1_3 )) ,
  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0)
|--
  (EX (resv: Z)  (l1: (@list Z)) ,
  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) ((@nil Z)))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  ((( &( "res" ) )) # Ptr  |-> resv)
  **  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0))
  ||
  (EX (unext: Z)  (resv_2: Z)  (l1_2: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  “ (node_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x >= a) ” 
  &&  “ (l = (app (l1_2) ((cons (x) (l0))))) ” 
  &&  “ (strict_upperbound a l1_2 ) ”
  &&  ((( &( "res" ) )) # Ptr  |-> resv_2)
  **  (sllseg resv_2 node_pre l1_2 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 ))
.

Definition insertion_return_wit_1 := 
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) (PreH1 : (node_pre <> 0)) (PreH2 : (l = (app (l1) ((@nil Z))))) (PreH3 : (strict_upperbound a l1 )) ,
  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0)
|--
  EX (l0: (@list Z)) ,
  “ (l0 = (insert (a) (l))) ”
  &&  (sll resv l0 )
) \/
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) (PreH1 : (a <= INT_MAX)) (PreH2 : (a >= INT_MIN)) (PreH3 : (node_pre <> 0)) (PreH4 : (l = (app (l1) ((@nil Z))))) (PreH5 : (strict_upperbound a l1 )) ,
  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0)
|--
  (sll resv (insert (a) (l)) )
).

Definition insertion_return_wit_1_split_goal_spatial := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) (PreH1 : (a <= INT_MAX)) (PreH2 : (a >= INT_MIN)) (PreH3 : (node_pre <> 0)) (PreH4 : (l = (app (l1) ((@nil Z))))) (PreH5 : (strict_upperbound a l1 )) ,
  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0)
|--
  (sll resv (insert (a) (l)) )
.

Definition insertion_return_wit_2 := 
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) (x: Z) (l0_2: (@list Z)) (u: Z) (unext: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (u <> 0)) (PreH3 : (x >= a)) (PreH4 : (l = (app (l1) ((cons (x) (l0_2)))))) (PreH5 : (strict_upperbound a l1 )) ,
  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0_2 )
|--
  EX (l0: (@list Z)) ,
  “ (l0 = (insert (a) (l))) ”
  &&  (sll resv l0 )
) \/
(
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) (x: Z) (l0_2: (@list Z)) (u: Z) (unext: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (a <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (a >= INT_MIN)) (PreH5 : (node_pre <> 0)) (PreH6 : (u <> 0)) (PreH7 : (x >= a)) (PreH8 : (l = (app (l1) ((cons (x) (l0_2)))))) (PreH9 : (strict_upperbound a l1 )) ,
  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0_2 )
|--
  (sll resv (insert (a) (l)) )
).

Definition insertion_return_wit_2_split_goal_spatial := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) (x: Z) (l0_2: (@list Z)) (u: Z) (unext: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (a <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (a >= INT_MIN)) (PreH5 : (node_pre <> 0)) (PreH6 : (u <> 0)) (PreH7 : (x >= a)) (PreH8 : (l = (app (l1) ((cons (x) (l0_2)))))) (PreH9 : (strict_upperbound a l1 )) ,
  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0_2 )
|--
  (sll resv (insert (a) (l)) )
.

Definition insertion_partial_solve_wit_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p2_v <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (strict_upperbound a l1 )) ,
  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (p2_v <> 0) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (strict_upperbound a l1 ) ”
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

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
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l2 )
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
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) (l0_4: (@list Z)) (retval: Z) (PreH1 : (l0_4 = (insert (x) (l0_2)))) (PreH2 : (l2_2 = (cons (x) (l0_3)))) (PreH3 : (p <> 0)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (Permutation l1_2 l0_2 )) (PreH6 : (increasing l0_2 )) ,
  (sll retval l0_4 )
  **  (sll y l0_3 )
  **  ((( &( "q" ) )) # Ptr  |-> y)
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  ((( &( "q" ) )) # Ptr  |->_)
  **  (sll retval l0 )
  **  (sll y l2 )
) \/
(
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (l0_4: (@list Z)) (PreH1 : (l0_4 = (insert (x) (l0_2)))) (PreH2 : (l2_2 = (cons (x) (l0_3)))) (PreH3 : (p <> 0)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (Permutation l1_2 l0_2 )) (PreH6 : (increasing l0_2 )) ,
  TT && emp 
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l0_3))) ” 
  &&  “ (Permutation l1 l0_4 ) ” 
  &&  “ (increasing l0_4 ) ”
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

Definition insertion_sort_partial_solve_wit_1 := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (p <> 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (Permutation l1 l0 )) (PreH4 : (increasing l0 )) ,
  (sll res l0 )
  **  (sll p l2 )
|--
  EX (y: Z)  (l0_2: (@list Z))  (x: Z) ,
  “ (l2 = (cons (x) (l0_2))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll res l0 )
.

Definition insertion_sort_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0_2: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0_2)))) (PreH2 : (p <> 0)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (Permutation l1 l0 )) (PreH5 : (increasing l0 )) ,
  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> y)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ (p <> 0) ”
.

Definition insertion_sort_partial_solve_wit_2_aux := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0_2: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0_2)))) (PreH2 : (p <> 0)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (Permutation l1 l0 )) (PreH5 : (increasing l0 )) ,
  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll res l0 )
|--
  “ (p <> 0) ” 
  &&  “ (l2 = (cons (x) (l0_2))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll res l0 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sll y l0_2 )
.

Definition insertion_sort_partial_solve_wit_2 := insertion_sort_partial_solve_wit_2_pure -> insertion_sort_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include sll_Strategy_Correct.

Axiom proof_of_insertion_safety_wit_1 : insertion_safety_wit_1.
Axiom proof_of_insertion_entail_wit_1 : insertion_entail_wit_1.
Axiom proof_of_insertion_entail_wit_2 : insertion_entail_wit_2.
Axiom proof_of_insertion_entail_wit_3_1 : insertion_entail_wit_3_1.
Axiom proof_of_insertion_entail_wit_3_2 : insertion_entail_wit_3_2.
Axiom proof_of_insertion_entail_wit_4_1 : insertion_entail_wit_4_1.
Axiom proof_of_insertion_entail_wit_4_2 : insertion_entail_wit_4_2.
Axiom proof_of_insertion_return_wit_1 : insertion_return_wit_1.
Axiom proof_of_insertion_return_wit_2 : insertion_return_wit_2.
Axiom proof_of_insertion_partial_solve_wit_1 : insertion_partial_solve_wit_1.
Axiom proof_of_insertion_sort_safety_wit_1 : insertion_sort_safety_wit_1.
Axiom proof_of_insertion_sort_safety_wit_2 : insertion_sort_safety_wit_2.
Axiom proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Axiom proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Axiom proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_1 : insertion_sort_partial_solve_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_2_pure : insertion_sort_partial_solve_wit_2_pure.
Axiom proof_of_insertion_sort_partial_solve_wit_2 : insertion_sort_partial_solve_wit_2.

End VC_Correct.
