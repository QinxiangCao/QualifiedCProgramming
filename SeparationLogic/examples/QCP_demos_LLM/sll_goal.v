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
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

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
forall (p_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (pnext: Z) (pdata: Z) (n: Z) (p: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p <> 0)) (PreH4 : (l2 = (cons (pdata) (l3)))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> pdata)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> pnext)
  **  (sllseg p_pre p l1 )
  **  (sll pnext l3 )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
) \/
(
forall (p_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (pnext: Z) (pdata: Z) (n: Z) (p: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p <> 0)) (PreH4 : (l2 = (cons (pdata) (l3)))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> pdata)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> pnext)
  **  (sllseg p_pre p l1 )
  **  (sll pnext l3 )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
).

Definition length_safety_wit_2_split_goal_1 := 
forall (p_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (pnext: Z) (pdata: Z) (n: Z) (p: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p <> 0)) (PreH4 : (l2 = (cons (pdata) (l3)))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> pdata)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> pnext)
  **  (sllseg p_pre p l1 )
  **  (sll pnext l3 )
|--
  “ ((n + 1 ) <= INT_MAX) ”
.

Definition length_safety_wit_2_split_goal_2 := 
forall (p_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (pnext: Z) (pdata: Z) (n: Z) (p: Z) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p <> 0)) (PreH4 : (l2 = (cons (pdata) (l3)))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> pdata)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> pnext)
  **  (sllseg p_pre p l1 )
  **  (sll pnext l3 )
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
  &&  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ (0 = (Zlength (l1))) ”
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
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (l = (app (l1_2) (l2_2)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1_2)))) (PreH4 : (p <> 0)) ,
  (sllseg p_pre p l1_2 )
  **  (sll p l2_2 )
|--
  EX (pnext: Z)  (pdata: Z)  (l3: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (n = (Zlength (l1))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (l2 = (cons (pdata) (l3))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> pdata)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> pnext)
  **  (sllseg p_pre p l1 )
  **  (sll pnext l3 )
.

Definition length_entail_wit_3 := 
(
forall (p_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3: (@list Z)) (pnext: Z) (pdata: Z) (n: Z) (p: Z) (PreH1 : (l = (app (l1_2) (l2_2)))) (PreH2 : (n = (Zlength (l1_2)))) (PreH3 : (p <> 0)) (PreH4 : (l2_2 = (cons (pdata) (l3)))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> pdata)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> pnext)
  **  (sllseg p_pre p l1_2 )
  **  (sll pnext l3 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ ((n + 1 ) = (Zlength (l1))) ”
  &&  (sllseg p_pre pnext l1 )
  **  (sll pnext l2 )
) \/
(
forall (p_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3: (@list Z)) (pnext: Z) (pdata: Z) (n: Z) (p: Z) (PreH1 : (pdata <= INT_MAX)) (PreH2 : (pdata >= INT_MIN)) (PreH3 : (l = (app (l1_2) (l2_2)))) (PreH4 : (n = (Zlength (l1_2)))) (PreH5 : (p <> 0)) (PreH6 : (l2_2 = (cons (pdata) (l3)))) (PreH7 : ((Zlength (l)) <= INT_MAX)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> pdata)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> pnext)
  **  (sllseg p_pre p l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (l = (app (l1) (l3))) ” 
  &&  “ ((Zlength (l)) <= INT_MAX) ” 
  &&  “ ((n + 1 ) = (Zlength (l1))) ”
  &&  (sllseg p_pre pnext l1 )
).

Definition length_return_wit_1 := 
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (n = (Zlength (l))) ”
  &&  (sll p_pre l )
) \/
(
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (n = (Zlength (l))) ”
  &&  (sll p_pre l )
).

Definition length_return_wit_1_split_goal_1 := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  “ (n = (Zlength (l))) ”
.

Definition length_return_wit_1_split_goal_spatial := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = 0)) ,
  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  (sll p_pre l )
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
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) ,
  (sll w l1_2 )
  **  (sll v l2_2 )
|--
  EX (vnext: Z)  (vdata: Z)  (l2_new: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v <> 0) ” 
  &&  “ (l2 = (cons (vdata) (l2_new))) ”
  &&  (sll w l1 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> vnext)
  **  (sll vnext l2_new )
.

Definition reverse_entail_wit_3 := 
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l2_new: (@list Z)) (vnext: Z) (vdata: Z) (v: Z) (w: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (vdata) (l2_new)))) ,
  (sll w l1_2 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll vnext l2_new )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v l1 )
  **  (sll vnext l2 )
) \/
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l2_new: (@list Z)) (vdata: Z) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (vdata) (l2_new)))) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (vdata) (l1_2))))) (l2_new))) ”
  &&  emp
).

Definition reverse_entail_wit_3_split_goal_1 := 
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l2_new: (@list Z)) (vdata: Z) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (vdata) (l2_new)))) ,
  (l = (app ((rev ((cons (vdata) (l1_2))))) (l2_new)))
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
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) ,
  (sll w l1_2 )
  **  (sll v l2_2 )
|--
  EX (vn: Z)  (x: Z)  (xs: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v <> 0) ” 
  &&  “ (l2 = (cons (x) (xs))) ”
  &&  (sll w l1 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> vn)
  **  (sll vn xs )
.

Definition reverse_alter_style1_entail_wit_3 := 
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (xs: (@list Z)) (vn: Z) (v: Z) (w: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
  (sll w l1_2 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll vn xs )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v l1 )
  **  (sll vn l2 )
) \/
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (xs: (@list Z)) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (x) (l1_2))))) (xs))) ”
  &&  emp
).

Definition reverse_alter_style1_entail_wit_3_split_goal_1 := 
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (xs: (@list Z)) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
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
forall (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v_inv <> 0)) ,
  (sll w_inv l1_2 )
  **  (sll v_inv l2_2 )
|--
  EX (v_inv_next: Z)  (x: Z)  (xs: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v_inv <> 0) ” 
  &&  “ (l2 = (cons (x) (xs))) ”
  &&  (sll w_inv l1 )
  **  ((&((v_inv)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v_inv)  # "list" ->ₛ "next")) # Ptr  |-> v_inv_next)
  **  (sll v_inv_next xs )
.

Definition reverse_alter_style2_entail_wit_3 := 
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (w_inv: Z) (v_inv: Z) (x: Z) (xs: (@list Z)) (v_inv_next: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v_inv <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
  (sll w_inv l1_2 )
  **  ((&((v_inv)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v_inv)  # "list" ->ₛ "next")) # Ptr  |-> w_inv)
  **  (sll v_inv_next xs )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v_inv l1 )
  **  (sll v_inv_next l2 )
) \/
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_inv: Z) (x: Z) (xs: (@list Z)) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v_inv <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (x) (l1_2))))) (xs))) ”
  &&  emp
).

Definition reverse_alter_style2_entail_wit_3_split_goal_1 := 
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_inv: Z) (x: Z) (xs: (@list Z)) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v_inv <> 0)) (PreH3 : (l2_2 = (cons (x) (xs)))) ,
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
  “ (0 = 0) ” 
  &&  “ (p_pre = p_pre) ”
  &&  (sll 0 (@nil Z) )
  **  (sll p_pre l )
.

Definition reverse_alter_style3_entail_wit_2 := 
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

Definition reverse_alter_style3_entail_wit_2_split_goal_1 := 
forall (p_pre: Z) (l: (@list Z)) (w: Z) (v: Z) (PreH1 : (w = 0)) (PreH2 : (w = 0)) (PreH3 : (v = p_pre)) ,
  (l = (app ((rev ((@nil Z)))) (l)))
.

Definition reverse_alter_style3_entail_wit_3 := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) ,
  (sll w l1_2 )
  **  (sll v l2_2 )
|--
  EX (vnext: Z)  (vdata: Z)  (l2_new: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ” 
  &&  “ (v <> 0) ” 
  &&  “ (l2 = (cons (vdata) (l2_new))) ”
  &&  (sll w l1 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> vnext)
  **  (sll vnext l2_new )
.

Definition reverse_alter_style3_entail_wit_4 := 
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l2_new: (@list Z)) (vnext: Z) (vdata: Z) (v: Z) (w: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (vdata) (l2_new)))) ,
  (sll w l1_2 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll vnext l2_new )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app ((rev (l1))) (l2))) ”
  &&  (sll v l1 )
  **  (sll vnext l2 )
) \/
(
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l2_new: (@list Z)) (vdata: Z) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (vdata) (l2_new)))) ,
  TT && emp 
|--
  “ (l = (app ((rev ((cons (vdata) (l1_2))))) (l2_new))) ”
  &&  emp
).

Definition reverse_alter_style3_entail_wit_4_split_goal_1 := 
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l2_new: (@list Z)) (vdata: Z) (v: Z) (PreH1 : (l = (app ((rev (l1_2))) (l2_2)))) (PreH2 : (v <> 0)) (PreH3 : (l2_2 = (cons (vdata) (l2_new)))) ,
  (l = (app ((rev ((cons (vdata) (l1_2))))) (l2_new)))
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
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH2 : (x_pre <> 0)) (PreH3 : (t <> 0)) (PreH4 : (t_next = u)) ,
  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  (sllseg x_pre t l1a )
  **  (sll u l1b )
  **  (sll y_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre <> 0)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  EX (xn: Z)  (a: Z)  (l1n: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (l1 = (cons (a) (l1n))) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1n )
  **  (sll y_pre l2 )
.

Definition append_entail_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (a: Z) (l1n: (@list Z)) (xn: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (l1 = (cons (a) (l1n)))) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1n )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (t_data: Z)  (l1b: (@list Z)) ,
  “ ((app (l1a) ((cons (t_data) (l1b)))) = l1) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (t_next = xn) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre x_pre l1a )
  **  (sll xn l1b )
  **  (sll y_pre l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (a: Z) (l1n: (@list Z)) (PreH1 : (x_pre <> 0)) (PreH2 : (l1 = (cons (a) (l1n)))) ,
  TT && emp 
|--
  “ ((app ((@nil Z)) ((cons (a) (l1n)))) = l1) ”
  &&  emp
).

Definition append_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (l1: (@list Z)) (a: Z) (l1n: (@list Z)) (PreH1 : (x_pre <> 0)) (PreH2 : (l1 = (cons (a) (l1n)))) ,
  ((app ((@nil Z)) ((cons (a) (l1n)))) = l1)
.

Definition append_entail_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next_2: Z) (l1a_2: (@list Z)) (t_data_2: Z) (t: Z) (l1b_2: (@list Z)) (PreH1 : (u <> 0)) (PreH2 : ((app (l1a_2) ((cons (t_data_2) (l1b_2)))) = l1)) (PreH3 : (x_pre <> 0)) (PreH4 : (t <> 0)) (PreH5 : (t_next_2 = u)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x_pre t l1a_2 )
  **  (sll u l1b_2 )
  **  (sll y_pre l2 )
|--
  EX (unext: Z)  (udata: Z)  (l1b_new: (@list Z))  (t_next: Z)  (l1a: (@list Z))  (t_data: Z)  (l1b: (@list Z)) ,
  “ ((app (l1a) ((cons (t_data) (l1b)))) = l1) ” 
  &&  “ (t <> 0) ” 
  &&  “ (t_next = u) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (l1b = (cons (udata) (l1b_new))) ”
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre t l1a )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> udata)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l1b_new )
  **  (sll y_pre l2 )
.

Definition append_entail_wit_4 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l1a_2: (@list Z)) (l1b_2: (@list Z)) (l1b_new: (@list Z)) (udata: Z) (unext: Z) (t: Z) (t_data_2: Z) (t_next_2: Z) (u: Z) (PreH1 : ((app (l1a_2) ((cons (t_data_2) (l1b_2)))) = l1)) (PreH2 : (t <> 0)) (PreH3 : (t_next_2 = u)) (PreH4 : (u <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (l1b_2 = (cons (udata) (l1b_new)))) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x_pre t l1a_2 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> udata)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l1b_new )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (t_data: Z)  (l1b: (@list Z)) ,
  “ ((app (l1a) ((cons (t_data) (l1b)))) = l1) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (t_next = unext) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre u l1a )
  **  (sll unext l1b )
  **  (sll y_pre l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (l1a_2: (@list Z)) (l1b_2: (@list Z)) (l1b_new: (@list Z)) (udata: Z) (t: Z) (t_data_2: Z) (t_next_2: Z) (u: Z) (PreH1 : (t_data_2 <= INT_MAX)) (PreH2 : (t_data_2 >= INT_MIN)) (PreH3 : ((app (l1a_2) ((cons (t_data_2) (l1b_2)))) = l1)) (PreH4 : (t <> 0)) (PreH5 : (t_next_2 = u)) (PreH6 : (u <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (l1b_2 = (cons (udata) (l1b_new)))) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x_pre t l1a_2 )
|--
  EX (l1a: (@list Z)) ,
  “ ((app (l1a) ((cons (udata) (l1b_new)))) = l1) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ”
  &&  (sllseg x_pre u l1a )
).

Definition append_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : (u = 0)) (PreH2 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH3 : (x_pre <> 0)) (PreH4 : (t <> 0)) (PreH5 : (t_next = u)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (sllseg x_pre t l1a )
  **  (sll u l1b )
  **  (sll y_pre l2 )
|--
  (sll x_pre (app (l1) (l2)) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) (PreH1 : (t_data <= INT_MAX)) (PreH2 : (t_data >= INT_MIN)) (PreH3 : (u = 0)) (PreH4 : ((app (l1a) ((cons (t_data) (l1b)))) = l1)) (PreH5 : (x_pre <> 0)) (PreH6 : (t <> 0)) (PreH7 : (t_next = u)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (sllseg x_pre t l1a )
  **  (sll u l1b )
  **  (sll y_pre l2 )
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ ((app (l1) (l2)) = (cons (x) (l0))) ”
  &&  (sll y l0 )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
).

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
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (l1 = (cons (a) (l1b)))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "u" ) )) # Ptr  |-> xn)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_long_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH2 : (t_next = u)) (PreH3 : (t <> 0)) (PreH4 : (x_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sllseg x_pre t l1a )
  **  (sll u l1c )
  **  (sll y_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_long_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (x_pre <> 0)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  EX (xn: Z)  (a: Z)  (l1b: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (l1 = (cons (a) (l1b))) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
.

Definition append_long_entail_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (xn <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (l1 = (cons (a) (l1b)))) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (b: Z)  (l1c: (@list Z)) ,
  “ ((app (l1a) ((cons (b) (l1c)))) = l1) ” 
  &&  “ (t_next = xn) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre x_pre l1a )
  **  (sll xn l1c )
  **  (sll y_pre l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (xn <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (l1 = (cons (a) (l1b)))) ,
  TT && emp 
|--
  “ ((app ((@nil Z)) ((cons (a) (l1b)))) = l1) ”
  &&  emp
).

Definition append_long_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (xn <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (l1 = (cons (a) (l1b)))) ,
  ((app ((@nil Z)) ((cons (a) (l1b)))) = l1)
.

Definition append_long_entail_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next_2: Z) (t: Z) (l1a_2: (@list Z)) (b_2: Z) (l1c_2: (@list Z)) (PreH1 : (u <> 0)) (PreH2 : ((app (l1a_2) ((cons (b_2) (l1c_2)))) = l1)) (PreH3 : (t_next_2 = u)) (PreH4 : (t <> 0)) (PreH5 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x_pre t l1a_2 )
  **  (sll u l1c_2 )
  **  (sll y_pre l2 )
|--
  EX (un: Z)  (c: Z)  (l1d: (@list Z))  (t_next: Z)  (l1a: (@list Z))  (b: Z)  (l1c: (@list Z)) ,
  “ ((app (l1a) ((cons (b) (l1c)))) = l1) ” 
  &&  “ (t_next = u) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (l1c = (cons (c) (l1d))) ”
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> c)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> un)
  **  (sllseg x_pre t l1a )
  **  (sll un l1d )
  **  (sll y_pre l2 )
.

Definition append_long_entail_wit_4 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l1a_2: (@list Z)) (b_2: Z) (l1c_2: (@list Z)) (l1d: (@list Z)) (c: Z) (un: Z) (t: Z) (t_next_2: Z) (u: Z) (PreH1 : ((app (l1a_2) ((cons (b_2) (l1c_2)))) = l1)) (PreH2 : (t_next_2 = u)) (PreH3 : (t <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (u <> 0)) (PreH6 : (l1c_2 = (cons (c) (l1d)))) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> c)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> un)
  **  (sllseg x_pre t l1a_2 )
  **  (sll un l1d )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (b: Z)  (l1c: (@list Z)) ,
  “ ((app (l1a) ((cons (b) (l1c)))) = l1) ” 
  &&  “ (t_next = un) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre u l1a )
  **  (sll un l1c )
  **  (sll y_pre l2 )
) \/
(
forall (x_pre: Z) (l1: (@list Z)) (l1a_2: (@list Z)) (b_2: Z) (l1c_2: (@list Z)) (l1d: (@list Z)) (c: Z) (t: Z) (t_next_2: Z) (u: Z) (PreH1 : (b_2 <= INT_MAX)) (PreH2 : (b_2 >= INT_MIN)) (PreH3 : ((app (l1a_2) ((cons (b_2) (l1c_2)))) = l1)) (PreH4 : (t_next_2 = u)) (PreH5 : (t <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (u <> 0)) (PreH8 : (l1c_2 = (cons (c) (l1d)))) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x_pre t l1a_2 )
|--
  EX (l1a: (@list Z)) ,
  “ ((app (l1a) ((cons (c) (l1d)))) = l1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x_pre u l1a )
).

Definition append_long_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : (u = 0)) (PreH2 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH3 : (t_next = u)) (PreH4 : (t <> 0)) (PreH5 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (sllseg x_pre t l1a )
  **  (sll u l1c )
  **  (sll y_pre l2 )
|--
  (sll x_pre (app (l1) (l2)) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) (PreH1 : (b <= INT_MAX)) (PreH2 : (b >= INT_MIN)) (PreH3 : (u = 0)) (PreH4 : ((app (l1a) ((cons (b) (l1c)))) = l1)) (PreH5 : (t_next = u)) (PreH6 : (t <> 0)) (PreH7 : (x_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (sllseg x_pre t l1a )
  **  (sll u l1c )
  **  (sll y_pre l2 )
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ ((app (l1) (l2)) = (cons (x) (l0))) ”
  &&  (sll y l0 )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
).

Definition append_long_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (xn = 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (l1 = (cons (a) (l1b)))) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
|--
  (sll x_pre (app (l1) (l2)) )
) \/
(
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (xn = 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (l1 = (cons (a) (l1b)))) ,
  (sll xn l1b )
|--
  “ ((app (l1) (l2)) = (cons (a) (l2))) ”
  &&  emp
).

Definition append_long_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (xn = 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (l1 = (cons (a) (l1b)))) ,
  (sll xn l1b )
|--
  “ ((app (l1) (l2)) = (cons (a) (l2))) ”
.

Definition append_long_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (l1: (@list Z)) (a: Z) (l1b: (@list Z)) (xn: Z) (PreH1 : (xn = 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (l1 = (cons (a) (l1b)))) ,
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
forall (y_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ptvv_2: Z) (ptv: Z) (l1a_2: (@list Z)) (l1b_2: (@list Z)) (PreH1 : ((app (l1a_2) (l1b_2)) = l1)) (PreH2 : (ptvv_2 <> 0)) ,
  ((ptv) # Ptr  |-> ptvv_2)
  **  (sllbseg ( &( "x" ) ) ptv l1a_2 )
  **  (sll ptvv_2 l1b_2 )
  **  (sll y_pre l2 )
|--
  EX (ptvv: Z)  (l1a: (@list Z))  (l1b: (@list Z)) ,
  “ ((app (l1a) (l1b)) = l1) ”
  &&  ((&((ptvv_2)  # "list" ->ₛ "next")) # Ptr  |-> ptvv)
  **  (sllbseg ( &( "x" ) ) &((ptvv_2)  # "list" ->ₛ "next") l1a )
  **  (sll ptvv l1b )
  **  (sll y_pre l2 )
) \/
(
forall (l1: (@list Z)) (ptvv_2: Z) (ptv: Z) (l1a_2: (@list Z)) (l1b_2: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (l1b_2 = (cons (x) (l0)))) (PreH4 : ((app (l1a_2) (l1b_2)) = l1)) (PreH5 : (ptvv_2 <> 0)) ,
  ((&((ptvv_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((ptv) # Ptr  |-> ptvv_2)
  **  (sllbseg ( &( "x" ) ) ptv l1a_2 )
|--
  EX (l1a: (@list Z)) ,
  “ ((app (l1a) (l0)) = l1) ”
  &&  (sllbseg ( &( "x" ) ) &((ptvv_2)  # "list" ->ₛ "next") l1a )
).

Definition append_2p_entail_wit_3 := 
(
forall (y_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ptvv: Z) (ptv: Z) (l1a: (@list Z)) (l1b: (@list Z)) (PreH1 : ((app (l1a) (l1b)) = l1)) (PreH2 : (ptvv = 0)) ,
  ((ptv) # Ptr  |-> y_pre)
  **  (sllbseg ( &( "x" ) ) ptv l1a )
  **  (sll ptvv l1b )
  **  (sll y_pre l2 )
|--
  EX (presv: Z) ,
  ((( &( "x" ) )) # Ptr  |-> presv)
  **  (sllseg presv y_pre l1 )
  **  (sll y_pre l2 )
) \/
(
forall (y_pre: Z) (l1: (@list Z)) (ptvv: Z) (ptv: Z) (l1a: (@list Z)) (l1b: (@list Z)) (PreH1 : ((app (l1a) (l1b)) = l1)) (PreH2 : (ptvv = 0)) ,
  ((ptv) # Ptr  |-> y_pre)
  **  (sllbseg ( &( "x" ) ) ptv l1a )
  **  (sll ptvv l1b )
|--
  EX (presv: Z) ,
  ((( &( "x" ) )) # Ptr  |-> presv)
  **  (sllseg presv y_pre l1 )
).

Definition append_2p_return_wit_1 := 
(
forall (y_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (presv: Z) ,
  (sllseg presv y_pre l1 )
  **  (sll y_pre l2 )
|--
  (sll presv (app (l1) (l2)) )
) \/
(
forall (y_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (presv: Z) ,
  (sllseg presv y_pre l1 )
  **  (sll y_pre l2 )
|--
  (sll presv (app (l1) (l2)) )
).

Definition append_2p_return_wit_1_split_goal_spatial := 
forall (y_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (presv: Z) ,
  (sllseg presv y_pre l1 )
  **  (sll y_pre l2 )
|--
  (sll presv (app (l1) (l2)) )
.

Module Type VC_Correct.

Include sll_Strategy_Correct.

Axiom proof_of_length_safety_wit_1 : length_safety_wit_1.
Axiom proof_of_length_safety_wit_2 : length_safety_wit_2.
Axiom proof_of_length_entail_wit_1 : length_entail_wit_1.
Axiom proof_of_length_entail_wit_2 : length_entail_wit_2.
Axiom proof_of_length_entail_wit_3 : length_entail_wit_3.
Axiom proof_of_length_return_wit_1 : length_return_wit_1.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_entail_wit_3 : reverse_entail_wit_3.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_alter_style1_safety_wit_1 : reverse_alter_style1_safety_wit_1.
Axiom proof_of_reverse_alter_style1_entail_wit_1 : reverse_alter_style1_entail_wit_1.
Axiom proof_of_reverse_alter_style1_entail_wit_2 : reverse_alter_style1_entail_wit_2.
Axiom proof_of_reverse_alter_style1_entail_wit_3 : reverse_alter_style1_entail_wit_3.
Axiom proof_of_reverse_alter_style1_return_wit_1 : reverse_alter_style1_return_wit_1.
Axiom proof_of_reverse_alter_style2_safety_wit_1 : reverse_alter_style2_safety_wit_1.
Axiom proof_of_reverse_alter_style2_entail_wit_1 : reverse_alter_style2_entail_wit_1.
Axiom proof_of_reverse_alter_style2_entail_wit_2 : reverse_alter_style2_entail_wit_2.
Axiom proof_of_reverse_alter_style2_entail_wit_3 : reverse_alter_style2_entail_wit_3.
Axiom proof_of_reverse_alter_style2_return_wit_1 : reverse_alter_style2_return_wit_1.
Axiom proof_of_reverse_alter_style3_safety_wit_1 : reverse_alter_style3_safety_wit_1.
Axiom proof_of_reverse_alter_style3_entail_wit_1 : reverse_alter_style3_entail_wit_1.
Axiom proof_of_reverse_alter_style3_entail_wit_2 : reverse_alter_style3_entail_wit_2.
Axiom proof_of_reverse_alter_style3_entail_wit_3 : reverse_alter_style3_entail_wit_3.
Axiom proof_of_reverse_alter_style3_entail_wit_4 : reverse_alter_style3_entail_wit_4.
Axiom proof_of_reverse_alter_style3_return_wit_1 : reverse_alter_style3_return_wit_1.
Axiom proof_of_append_safety_wit_1 : append_safety_wit_1.
Axiom proof_of_append_safety_wit_2 : append_safety_wit_2.
Axiom proof_of_append_entail_wit_1 : append_entail_wit_1.
Axiom proof_of_append_entail_wit_2 : append_entail_wit_2.
Axiom proof_of_append_entail_wit_3 : append_entail_wit_3.
Axiom proof_of_append_entail_wit_4 : append_entail_wit_4.
Axiom proof_of_append_return_wit_1 : append_return_wit_1.
Axiom proof_of_append_return_wit_2 : append_return_wit_2.
Axiom proof_of_append_long_safety_wit_1 : append_long_safety_wit_1.
Axiom proof_of_append_long_safety_wit_2 : append_long_safety_wit_2.
Axiom proof_of_append_long_safety_wit_3 : append_long_safety_wit_3.
Axiom proof_of_append_long_entail_wit_1 : append_long_entail_wit_1.
Axiom proof_of_append_long_entail_wit_2 : append_long_entail_wit_2.
Axiom proof_of_append_long_entail_wit_3 : append_long_entail_wit_3.
Axiom proof_of_append_long_entail_wit_4 : append_long_entail_wit_4.
Axiom proof_of_append_long_return_wit_1 : append_long_return_wit_1.
Axiom proof_of_append_long_return_wit_2 : append_long_return_wit_2.
Axiom proof_of_append_long_return_wit_3 : append_long_return_wit_3.
Axiom proof_of_append_2p_entail_wit_1 : append_2p_entail_wit_1.
Axiom proof_of_append_2p_entail_wit_2 : append_2p_entail_wit_2.
Axiom proof_of_append_2p_entail_wit_3 : append_2p_entail_wit_3.
Axiom proof_of_append_2p_return_wit_1 : append_2p_return_wit_1.

End VC_Correct.
