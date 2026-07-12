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
Require Import SimpleC.EE.Applications_human.fme.fme_lib.
Local Open Scope sac.
Require Import fme_strategy_goal.
Require Import fme_strategy_proof.

(*----- Function gcd -----*)

Definition gcd_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (0 < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gcd_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) ” 
  &&  “ (b_pre <> 0) ”
.

Definition gcd_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = 0)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (a_pre = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = 0)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (a_pre = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition gcd_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = 0)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  (a_pre = (Zgcd (a_pre) (b_pre)))
.

Definition gcd_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (b_pre <> 0)) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (b_pre <> 0)) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (retval = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition gcd_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) ))))) (PreH2 : (b_pre <> 0)) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  (retval = (Zgcd (a_pre) (b_pre)))
.

Definition gcd_partial_solve_wit_1_pure := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ” 
  &&  “ (0 <= (a_pre % ( b_pre ) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= INT_MIN)) (PreH2 : (b_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= (a_pre % ( b_pre ) )) ” 
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ”
).

Definition gcd_partial_solve_wit_1_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= INT_MIN)) (PreH2 : (b_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= (a_pre % ( b_pre ) )) ”
.

Definition gcd_partial_solve_wit_1_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= INT_MIN)) (PreH2 : (b_pre >= INT_MIN)) (PreH3 : (b_pre <> 0)) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ”
.

Definition gcd_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ ((a_pre % ( b_pre ) ) <= INT_MAX) ” 
  &&  “ (0 <= (a_pre % ( b_pre ) )) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  emp
.

Definition gcd_partial_solve_wit_1 := gcd_partial_solve_wit_1_pure -> gcd_partial_solve_wit_1_aux.

(*----- Function check_add_safe -----*)

Definition check_add_safe_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : ((-INT_MAX) <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : ((-INT_MAX) <= y_pre)) (PreH4 : (y_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_add_safe_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : ((-INT_MAX) <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((-INT_MAX) <= y_pre)) (PreH5 : (y_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((INT_MAX - x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (INT_MAX - x_pre )) ”
.

Definition check_add_safe_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : ((-INT_MAX) <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((-INT_MAX) <= y_pre)) (PreH5 : (y_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition check_add_safe_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : ((-INT_MAX) <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((-INT_MAX) <= y_pre)) (PreH5 : (y_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (((-INT_MAX) - x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - x_pre )) ”
.

Definition check_add_safe_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : ((-INT_MAX) <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((-INT_MAX) <= y_pre)) (PreH5 : (y_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition check_add_safe_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <= 0)) (PreH2 : ((-INT_MAX) <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((-INT_MAX) <= y_pre)) (PreH5 : (y_pre <= INT_MAX)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition check_add_safe_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (y_pre < ((-INT_MAX) - x_pre ))) (PreH2 : (x_pre <= 0)) (PreH3 : ((-INT_MAX) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((-INT_MAX) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = 0) ”
  &&  emp
.

Definition check_add_safe_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (y_pre >= ((-INT_MAX) - x_pre ))) (PreH2 : (x_pre <= 0)) (PreH3 : ((-INT_MAX) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((-INT_MAX) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ ((-INT_MAX) <= (x_pre + y_pre )) ” 
  &&  “ ((x_pre + y_pre ) <= INT_MAX) ”
  &&  emp
.

Definition check_add_safe_return_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (y_pre > (INT_MAX - x_pre ))) (PreH2 : (x_pre > 0)) (PreH3 : ((-INT_MAX) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((-INT_MAX) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = 0) ”
  &&  emp
.

Definition check_add_safe_return_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (y_pre <= (INT_MAX - x_pre ))) (PreH2 : (x_pre > 0)) (PreH3 : ((-INT_MAX) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((-INT_MAX) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ ((-INT_MAX) <= (x_pre + y_pre )) ” 
  &&  “ ((x_pre + y_pre ) <= INT_MAX) ”
  &&  emp
.

(*----- Function NilInequList -----*)

Definition NilInequList_safety_wit_1 := 
  TT && emp 
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition NilInequList_return_wit_1 := 
  TT && emp 
|--
  “ (0 = 0) ”
  &&  emp
.

(*----- Function ConsInequList -----*)

Definition ConsInequList_return_wit_1 := 
forall (l_pre: Z) (c_pre: Z) (l0: (@list Constraint)) (c0: Constraint) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (c_pre <> 0)) ,
  ((&((retval)  # "InequList" ->ₛ "coef")) # Ptr  |-> c_pre)
  **  ((&((retval)  # "InequList" ->ₛ "next")) # Ptr  |-> l_pre)
  **  (coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
|--
  (InequList retval n (cons (c0) (l0)) )
.

Definition ConsInequList_partial_solve_wit_1 := 
forall (l_pre: Z) (c_pre: Z) (l0: (@list Constraint)) (c0: Constraint) (n: Z) (PreH1 : (c_pre <> 0)) ,
  (coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
|--
  “ (c_pre <> 0) ”
  &&  (coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
.

(*----- Function free_InequList -----*)

Definition free_InequList_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (InequList p_pre n l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_InequList_safety_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (l = (cons (x) (l0)))) (PreH3 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_InequList_safety_wit_3 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h = 0)) (PreH2 : (h <> 0)) (PreH3 : (l = (cons (x) (l0)))) (PreH4 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ False ”
.

Definition free_InequList_safety_wit_4 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (h <> 0)) (PreH3 : (l = (cons (x) (l0)))) (PreH4 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_InequList_return_wit_1 := 
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre = 0)) ,
  (InequList p_pre n l )
|--
  TT && emp 
) \/
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre = 0)) ,
  (InequList p_pre n l )
|--
  TT && emp 
).

Definition free_InequList_return_wit_1_split_goal_spatial := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre = 0)) ,
  (InequList p_pre n l )
|--
  TT && emp 
.

Definition free_InequList_return_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  TT && emp 
|--
  TT && emp 
.

Definition free_InequList_return_wit_3 := 
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  (InequList y n l0 )
|--
  TT && emp 
) \/
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  (InequList y n l0 )
|--
  TT && emp 
).

Definition free_InequList_return_wit_3_split_goal_spatial := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  (InequList y n l0 )
|--
  TT && emp 
.

Definition free_InequList_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre <> 0)) ,
  (InequList p_pre n l )
|--
  EX (h: Z)  (y: Z)  (l0: (@list Constraint))  (x: Constraint) ,
  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
.

Definition free_InequList_partial_solve_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (h <> 0)) (PreH3 : (l = (cons (x) (l0)))) (PreH4 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
|--
  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  (coef_array h n x )
  **  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_3 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (y <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_4 := 
forall (p_pre: Z) (l: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (y <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_5 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (y = 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n l0 )
.

(*----- Function eliminate -----*)

Definition eliminate_safety_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (PreH1 : (l = (app (l1) (l2)))) (PreH2 : (eliminate_xn num_pre l1 bp )) (PreH3 : (form_BP up lo re bp )) (PreH4 : (BP0 <> 0)) (PreH5 : (1 <= num_pre)) (PreH6 : (num_pre < n)) (PreH7 : (retval_3 = 0)) (PreH8 : (retval_2 = 0)) (PreH9 : (retval = 0)) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n)) (PreH12 : (BP0 <> 0)) (PreH13 : (LP_abs_in_int_range n l )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (InequList cur n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_2 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : (l2 = (cons (x) (l3)))) (PreH2 : (cur_coef <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (eliminate_xn num_pre l1 bp )) (PreH6 : (form_BP up lo re bp )) (PreH7 : (BP0 <> 0)) (PreH8 : (1 <= num_pre)) (PreH9 : (num_pre < n)) (PreH10 : (retval_3 = 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (retval = 0)) (PreH13 : (1 <= num_pre)) (PreH14 : (num_pre < n)) (PreH15 : (BP0 <> 0)) (PreH16 : (LP_abs_in_int_range n l )) ,
  (coef_array cur_coef n x )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_3 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) <> 0)) (PreH2 : (l2 = (cons (x) (l3)))) (PreH3 : (cur_coef <> 0)) (PreH4 : (cur <> 0)) (PreH5 : (l = (app (l1) (l2)))) (PreH6 : (eliminate_xn num_pre l1 bp )) (PreH7 : (form_BP up lo re bp )) (PreH8 : (BP0 <> 0)) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n)) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_2 = 0)) (PreH13 : (retval = 0)) (PreH14 : (1 <= num_pre)) (PreH15 : (num_pre < n)) (PreH16 : (BP0 <> 0)) (PreH17 : (LP_abs_in_int_range n l )) ,
  (coef_array cur_coef n x )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_entail_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval = 0)) (PreH4 : (1 <= num_pre)) (PreH5 : (num_pre < n)) (PreH6 : (BP0 <> 0)) (PreH7 : (LP_abs_in_int_range n l )) ,
  ((( &( "remain" ) )) # Ptr  |-> retval_3)
  **  ((( &( "lower" ) )) # Ptr  |-> retval_2)
  **  ((( &( "upper" ) )) # Ptr  |-> retval)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "upper" ) )) # Ptr  |-> 0)
  **  ((( &( "lower" ) )) # Ptr  |-> 0)
  **  ((( &( "remain" ) )) # Ptr  |-> 0)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_entail_wit_2 := 
(
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (0 = 0)) (PreH2 : (0 = 0)) (PreH3 : (0 = 0)) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : (retval = 0)) (PreH7 : (1 <= num_pre)) (PreH8 : (num_pre < n)) (PreH9 : (BP0 <> 0)) (PreH10 : (LP_abs_in_int_range n l )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up lo re bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList 0 n up )
  **  (InequList 0 n lo )
  **  (InequList 0 n re )
  **  (InequList r_pre n l2 )
) \/
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval = 0)) (PreH4 : (1 <= num_pre)) (PreH5 : (num_pre < n)) (PreH6 : (BP0 <> 0)) (PreH7 : (LP_abs_in_int_range n l )) ,
  TT && emp 
|--
  EX (bp: BP)  (l1: (@list Constraint)) ,
  “ (l = (app (l1) (l))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP (@nil Constraint) (@nil Constraint) (@nil Constraint) bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  emp
).

Definition eliminate_entail_wit_3_1 := 
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) <> 0)) (PreH3 : (l2_2 = (cons (x) (l3)))) (PreH4 : (cur_coef <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (l = (app (l1_2) (l2_2)))) (PreH7 : (eliminate_xn num_pre l1_2 bp_2 )) (PreH8 : (form_BP up_2 lo_2 re_2 bp_2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n)) (PreH12 : (retval_3 = 0)) (PreH13 : (retval_2 = 0)) (PreH14 : (retval = 0)) (PreH15 : (1 <= num_pre)) (PreH16 : (num_pre < n)) (PreH17 : (BP0 <> 0)) (PreH18 : (LP_abs_in_int_range n l )) ,
  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> upper)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up lo re bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList cur n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
  **  (InequList cur_next n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
) \/
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) <> 0)) (PreH3 : (l2_2 = (cons (x) (l3)))) (PreH4 : (cur_coef <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (l = (app (l1_2) (l2_2)))) (PreH7 : (eliminate_xn num_pre l1_2 bp_2 )) (PreH8 : (form_BP up_2 lo_2 re_2 bp_2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n)) (PreH12 : (retval_3 = 0)) (PreH13 : (retval_2 = 0)) (PreH14 : (retval = 0)) (PreH15 : (1 <= num_pre)) (PreH16 : (num_pre < n)) (PreH17 : (BP0 <> 0)) (PreH18 : (LP_abs_in_int_range n l )) ,
  TT && emp 
|--
  EX (bp: BP)  (l1: (@list Constraint)) ,
  “ (cur_coef <> 0) ” 
  &&  “ (l = (app (l1) (l3))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP (cons (x) (up_2)) lo_2 re_2 bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  emp
).

Definition eliminate_entail_wit_3_2 := 
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) <= 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) <> 0)) (PreH3 : (l2_2 = (cons (x) (l3)))) (PreH4 : (cur_coef <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (l = (app (l1_2) (l2_2)))) (PreH7 : (eliminate_xn num_pre l1_2 bp_2 )) (PreH8 : (form_BP up_2 lo_2 re_2 bp_2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n)) (PreH12 : (retval_3 = 0)) (PreH13 : (retval_2 = 0)) (PreH14 : (retval = 0)) (PreH15 : (1 <= num_pre)) (PreH16 : (num_pre < n)) (PreH17 : (BP0 <> 0)) (PreH18 : (LP_abs_in_int_range n l )) ,
  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> lower)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up lo re bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList cur n lo )
  **  (InequList remain n re )
  **  (InequList cur_next n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
) \/
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) <= 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) <> 0)) (PreH3 : (l2_2 = (cons (x) (l3)))) (PreH4 : (cur_coef <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (l = (app (l1_2) (l2_2)))) (PreH7 : (eliminate_xn num_pre l1_2 bp_2 )) (PreH8 : (form_BP up_2 lo_2 re_2 bp_2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n)) (PreH12 : (retval_3 = 0)) (PreH13 : (retval_2 = 0)) (PreH14 : (retval = 0)) (PreH15 : (1 <= num_pre)) (PreH16 : (num_pre < n)) (PreH17 : (BP0 <> 0)) (PreH18 : (LP_abs_in_int_range n l )) ,
  TT && emp 
|--
  EX (bp: BP)  (l1: (@list Constraint)) ,
  “ (cur_coef <> 0) ” 
  &&  “ (l = (app (l1) (l3))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up_2 (cons (x) (lo_2)) re_2 bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  emp
).

Definition eliminate_entail_wit_3_3 := 
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) = 0)) (PreH2 : (l2_2 = (cons (x) (l3)))) (PreH3 : (cur_coef <> 0)) (PreH4 : (cur <> 0)) (PreH5 : (l = (app (l1_2) (l2_2)))) (PreH6 : (eliminate_xn num_pre l1_2 bp_2 )) (PreH7 : (form_BP up_2 lo_2 re_2 bp_2 )) (PreH8 : (BP0 <> 0)) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n)) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_2 = 0)) (PreH13 : (retval = 0)) (PreH14 : (1 <= num_pre)) (PreH15 : (num_pre < n)) (PreH16 : (BP0 <> 0)) (PreH17 : (LP_abs_in_int_range n l )) ,
  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> remain)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up lo re bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList cur n re )
  **  (InequList cur_next n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
) \/
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) = 0)) (PreH2 : (l2_2 = (cons (x) (l3)))) (PreH3 : (cur_coef <> 0)) (PreH4 : (cur <> 0)) (PreH5 : (l = (app (l1_2) (l2_2)))) (PreH6 : (eliminate_xn num_pre l1_2 bp_2 )) (PreH7 : (form_BP up_2 lo_2 re_2 bp_2 )) (PreH8 : (BP0 <> 0)) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n)) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_2 = 0)) (PreH13 : (retval = 0)) (PreH14 : (1 <= num_pre)) (PreH15 : (num_pre < n)) (PreH16 : (BP0 <> 0)) (PreH17 : (LP_abs_in_int_range n l )) ,
  TT && emp 
|--
  EX (bp: BP)  (l1: (@list Constraint)) ,
  “ (cur_coef <> 0) ” 
  &&  “ (l = (app (l1) (l3))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up_2 lo_2 (cons (x) (re_2)) bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  emp
).

Definition eliminate_return_wit_1 := 
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (PreH1 : (cur = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (eliminate_xn num_pre l1 bp )) (PreH4 : (form_BP up_2 lo_2 re_2 bp )) (PreH5 : (BP0 <> 0)) (PreH6 : (1 <= num_pre)) (PreH7 : (num_pre < n)) (PreH8 : (retval_3 = 0)) (PreH9 : (retval_2 = 0)) (PreH10 : (retval = 0)) (PreH11 : (1 <= num_pre)) (PreH12 : (num_pre < n)) (PreH13 : (BP0 <> 0)) (PreH14 : (LP_abs_in_int_range n l )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> remain)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  (InequList cur n l2 )
|--
  EX (BP0_remain: Z)  (BP0_lower: Z)  (BP0_upper: Z)  (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (b: BP) ,
  “ (eliminate_xn num_pre l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos num_pre up ) ” 
  &&  “ (InequList_nth_neg num_pre lo ) ” 
  &&  “ (LP_abs_in_int_range n up ) ” 
  &&  “ (LP_abs_in_int_range n lo ) ” 
  &&  “ (LP_abs_in_int_range n re ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper n up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower n lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain n re )
) \/
(
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (PreH1 : (cur = 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (eliminate_xn num_pre l1 bp )) (PreH4 : (form_BP up_2 lo_2 re_2 bp )) (PreH5 : (BP0 <> 0)) (PreH6 : (1 <= num_pre)) (PreH7 : (num_pre < n)) (PreH8 : (retval_3 = 0)) (PreH9 : (retval_2 = 0)) (PreH10 : (retval = 0)) (PreH11 : (1 <= num_pre)) (PreH12 : (num_pre < n)) (PreH13 : (BP0 <> 0)) (PreH14 : (LP_abs_in_int_range n l )) ,
  (InequList cur n l2 )
|--
  EX (b: BP) ,
  “ (eliminate_xn num_pre l b ) ” 
  &&  “ (form_BP up_2 lo_2 re_2 b ) ” 
  &&  “ (InequList_nth_pos num_pre up_2 ) ” 
  &&  “ (InequList_nth_neg num_pre lo_2 ) ” 
  &&  “ (LP_abs_in_int_range n up_2 ) ” 
  &&  “ (LP_abs_in_int_range n lo_2 ) ” 
  &&  “ (LP_abs_in_int_range n re_2 ) ”
  &&  emp
).

Definition eliminate_partial_solve_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (PreH1 : (1 <= num_pre)) (PreH2 : (num_pre < n)) (PreH3 : (BP0 <> 0)) (PreH4 : (LP_abs_in_int_range n l )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_partial_solve_wit_2 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (1 <= num_pre)) (PreH3 : (num_pre < n)) (PreH4 : (BP0 <> 0)) (PreH5 : (LP_abs_in_int_range n l )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_partial_solve_wit_3 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval = 0)) (PreH3 : (1 <= num_pre)) (PreH4 : (num_pre < n)) (PreH5 : (BP0 <> 0)) (PreH6 : (LP_abs_in_int_range n l )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_partial_solve_wit_4_pure := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (PreH1 : (cur <> 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (eliminate_xn num_pre l1 bp )) (PreH4 : (form_BP up lo re bp )) (PreH5 : (BP0 <> 0)) (PreH6 : (1 <= num_pre)) (PreH7 : (num_pre < n)) (PreH8 : (retval_3 = 0)) (PreH9 : (retval_2 = 0)) (PreH10 : (retval = 0)) (PreH11 : (1 <= num_pre)) (PreH12 : (num_pre < n)) (PreH13 : (BP0 <> 0)) (PreH14 : (LP_abs_in_int_range n l )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (InequList cur n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (cur <> 0) ”
.

Definition eliminate_partial_solve_wit_4_aux := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (PreH1 : (cur <> 0)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (eliminate_xn num_pre l1 bp )) (PreH4 : (form_BP up lo re bp )) (PreH5 : (BP0 <> 0)) (PreH6 : (1 <= num_pre)) (PreH7 : (num_pre < n)) (PreH8 : (retval_3 = 0)) (PreH9 : (retval_2 = 0)) (PreH10 : (retval = 0)) (PreH11 : (1 <= num_pre)) (PreH12 : (num_pre < n)) (PreH13 : (BP0 <> 0)) (PreH14 : (LP_abs_in_int_range n l )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
  **  (InequList cur n l2 )
|--
  “ (cur <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up lo re bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  (InequList cur n l2 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
.

Definition eliminate_partial_solve_wit_4 := eliminate_partial_solve_wit_4_pure -> eliminate_partial_solve_wit_4_aux.

Definition eliminate_partial_solve_wit_5 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : (l2 = (cons (x) (l3)))) (PreH2 : (cur_coef <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (eliminate_xn num_pre l1 bp )) (PreH6 : (form_BP up lo re bp )) (PreH7 : (BP0 <> 0)) (PreH8 : (1 <= num_pre)) (PreH9 : (num_pre < n)) (PreH10 : (retval_3 = 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (retval = 0)) (PreH13 : (1 <= num_pre)) (PreH14 : (num_pre < n)) (PreH15 : (BP0 <> 0)) (PreH16 : (LP_abs_in_int_range n l )) ,
  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
|--
  “ (l2 = (cons (x) (l3))) ” 
  &&  “ (cur_coef <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up lo re bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  (((cur_coef + (num_pre * sizeof(INT)))) # Int  |-> (coef_Znth (num_pre) (x) (0)))
  **  (coef_array_missing_i_rec cur_coef num_pre 0 n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
.

Definition eliminate_partial_solve_wit_6 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) (PreH1 : ((coef_Znth (num_pre) (x) (0)) <> 0)) (PreH2 : (l2 = (cons (x) (l3)))) (PreH3 : (cur_coef <> 0)) (PreH4 : (cur <> 0)) (PreH5 : (l = (app (l1) (l2)))) (PreH6 : (eliminate_xn num_pre l1 bp )) (PreH7 : (form_BP up lo re bp )) (PreH8 : (BP0 <> 0)) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n)) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_2 = 0)) (PreH13 : (retval = 0)) (PreH14 : (1 <= num_pre)) (PreH15 : (num_pre < n)) (PreH16 : (BP0 <> 0)) (PreH17 : (LP_abs_in_int_range n l )) ,
  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
|--
  “ ((coef_Znth (num_pre) (x) (0)) <> 0) ” 
  &&  “ (l2 = (cons (x) (l3))) ” 
  &&  “ (cur_coef <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (eliminate_xn num_pre l1 bp ) ” 
  &&  “ (form_BP up lo re bp ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range n l ) ”
  &&  (((cur_coef + (num_pre * sizeof(INT)))) # Int  |-> (coef_Znth (num_pre) (x) (0)))
  **  (coef_array_missing_i_rec cur_coef num_pre 0 n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
.

Definition eliminate_which_implies_wit_1 := 
forall (n: Z) (l2: (@list Constraint)) (cur: Z) (PreH1 : (cur <> 0)) ,
  (InequList cur n l2 )
|--
  EX (cur_next: Z)  (cur_coef: Z)  (x: Constraint)  (l3: (@list Constraint)) ,
  “ (l2 = (cons (x) (l3))) ” 
  &&  “ (cur_coef <> 0) ”
  &&  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
.

(*----- Function generate_new_constr -----*)

Definition generate_new_constr_safety_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (PreH1 : (1 <= cur_num_pre)) (PreH2 : (cur_num_pre < (num_pre + 1 ))) (PreH3 : ((num_pre + 1 ) <= INT_MAX)) (PreH4 : (r1_pre <> 0)) (PreH5 : (r2_pre <> 0)) (PreH6 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH8 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH9 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |->_)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ ((coef_Znth (cur_num_pre) (c2) (0)) <> (INT_MIN)) ”
.

Definition generate_new_constr_safety_wit_2 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m1" ) )) # Int  |->_)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m1" ) )) # Int  |->_)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
).

Definition generate_new_constr_safety_wit_2_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m1" ) )) # Int  |->_)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) <> (INT_MIN)) \/ (retval <> (-1))) ”
.

Definition generate_new_constr_safety_wit_2_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m1" ) )) # Int  |->_)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (retval <> 0) ”
.

Definition generate_new_constr_safety_wit_3 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m2" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((coef_Znth (cur_num_pre) (c1) (0)) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m2" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((coef_Znth (cur_num_pre) (c1) (0)) <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
).

Definition generate_new_constr_safety_wit_3_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m2" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((coef_Znth (cur_num_pre) (c1) (0)) <> (INT_MIN)) \/ (retval <> (-1))) ”
.

Definition generate_new_constr_safety_wit_3_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m2" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (retval <> 0) ”
.

Definition generate_new_constr_safety_wit_4 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |->_)
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) ” 
  &&  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |->_)
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) ” 
  &&  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) ”
).

Definition generate_new_constr_safety_wit_4_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |->_)
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) ”
.

Definition generate_new_constr_safety_wit_4_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |->_)
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) ”
.

Definition generate_new_constr_safety_wit_5 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |->_)
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition generate_new_constr_safety_wit_6 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-INT_MAX) <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) ” 
  &&  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-INT_MAX) <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) ” 
  &&  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) ”
).

Definition generate_new_constr_safety_wit_6_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-INT_MAX) <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) ”
.

Definition generate_new_constr_safety_wit_6_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) ”
.

Definition generate_new_constr_safety_wit_7 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition generate_new_constr_safety_wit_8 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition generate_new_constr_safety_wit_9 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) ” 
  &&  “ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) ” 
  &&  “ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) ”
).

Definition generate_new_constr_safety_wit_9_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) ”
.

Definition generate_new_constr_safety_wit_9_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) ”
.

Definition generate_new_constr_safety_wit_10 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition generate_new_constr_safety_wit_11 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-INT_MAX) <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) ” 
  &&  “ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-INT_MAX) <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) ” 
  &&  “ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) ”
).

Definition generate_new_constr_safety_wit_11_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((-INT_MAX) <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) ”
.

Definition generate_new_constr_safety_wit_11_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) ”
.

Definition generate_new_constr_safety_wit_12 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition generate_new_constr_safety_wit_13 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition generate_new_constr_safety_wit_14 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lb2" ) )) # Int  |-> ((-INT_MAX) ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_15 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (PreH1 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH2 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH3 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : ((num_pre + 1 ) <= INT_MAX)) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) (PreH9 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH10 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH11 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH12 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "lb2" ) )) # Int  |-> ((-INT_MAX) ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_16 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c1) (0)) < lb1)) (PreH2 : (i <= num_pre)) (PreH3 : (m1v > 0)) (PreH4 : (m2v > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (num_pre + 1 ))) (PreH7 : (ub1 = (INT_MAX ÷ m1v ))) (PreH8 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH9 : (ub2 = (INT_MAX ÷ m2v ))) (PreH10 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH11 : (in_int_range i m1v c1 )) (PreH12 : (in_int_range i m2v c2 )) (PreH13 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH14 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH15 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH16 : (1 <= cur_num_pre)) (PreH17 : (cur_num_pre < (num_pre + 1 ))) (PreH18 : ((num_pre + 1 ) <= INT_MAX)) (PreH19 : (r1_pre <> 0)) (PreH20 : (r2_pre <> 0)) (PreH21 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH23 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH24 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_17 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c1) (0)) > ub1)) (PreH2 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH3 : (i <= num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_18 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) < lb2)) (PreH2 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH3 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH4 : (i <= num_pre)) (PreH5 : (m1v > 0)) (PreH6 : (m2v > 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (num_pre + 1 ))) (PreH9 : (ub1 = (INT_MAX ÷ m1v ))) (PreH10 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH11 : (ub2 = (INT_MAX ÷ m2v ))) (PreH12 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH13 : (in_int_range i m1v c1 )) (PreH14 : (in_int_range i m2v c2 )) (PreH15 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH16 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH17 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH18 : (1 <= cur_num_pre)) (PreH19 : (cur_num_pre < (num_pre + 1 ))) (PreH20 : ((num_pre + 1 ) <= INT_MAX)) (PreH21 : (r1_pre <> 0)) (PreH22 : (r2_pre <> 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH25 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH26 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_19 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) > ub2)) (PreH2 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH3 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH4 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (ub1 = (INT_MAX ÷ m1v ))) (PreH11 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH12 : (ub2 = (INT_MAX ÷ m2v ))) (PreH13 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH14 : (in_int_range i m1v c1 )) (PreH15 : (in_int_range i m2v c2 )) (PreH16 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH17 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH18 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH19 : (1 <= cur_num_pre)) (PreH20 : (cur_num_pre < (num_pre + 1 ))) (PreH21 : ((num_pre + 1 ) <= INT_MAX)) (PreH22 : (r1_pre <> 0)) (PreH23 : (r2_pre <> 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH25 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH26 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH27 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_20 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) <= ub2)) (PreH2 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH3 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH4 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (ub1 = (INT_MAX ÷ m1v ))) (PreH11 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH12 : (ub2 = (INT_MAX ÷ m2v ))) (PreH13 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH14 : (in_int_range i m1v c1 )) (PreH15 : (in_int_range i m2v c2 )) (PreH16 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH17 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH18 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH19 : (1 <= cur_num_pre)) (PreH20 : (cur_num_pre < (num_pre + 1 ))) (PreH21 : ((num_pre + 1 ) <= INT_MAX)) (PreH22 : (r1_pre <> 0)) (PreH23 : (r2_pre <> 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH25 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH26 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH27 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition generate_new_constr_safety_wit_21 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : (i > num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (ub1 = (INT_MAX ÷ m1v ))) (PreH7 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH8 : (ub2 = (INT_MAX ÷ m2v ))) (PreH9 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH10 : (in_int_range i m1v c1 )) (PreH11 : (in_int_range i m2v c2 )) (PreH12 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH13 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH14 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH15 : (1 <= cur_num_pre)) (PreH16 : (cur_num_pre < (num_pre + 1 ))) (PreH17 : ((num_pre + 1 ) <= INT_MAX)) (PreH18 : (r1_pre <> 0)) (PreH19 : (r2_pre <> 0)) (PreH20 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH21 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH22 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH23 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num_pre + 1 )) ”
.

Definition generate_new_constr_safety_wit_22 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : (i > num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (ub1 = (INT_MAX ÷ m1v ))) (PreH7 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH8 : (ub2 = (INT_MAX ÷ m2v ))) (PreH9 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH10 : (in_int_range i m1v c1 )) (PreH11 : (in_int_range i m2v c2 )) (PreH12 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH13 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH14 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH15 : (1 <= cur_num_pre)) (PreH16 : (cur_num_pre < (num_pre + 1 ))) (PreH17 : ((num_pre + 1 ) <= INT_MAX)) (PreH18 : (r1_pre <> 0)) (PreH19 : (r2_pre <> 0)) (PreH20 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH21 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH22 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH23 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition generate_new_constr_safety_wit_23 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (abs_in_int_range (num_pre + 1 ) l )) (PreH3 : (i > num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array retval_2 (num_pre + 1 ) l )
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_24 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m2v * (coef_Znth (i) (c2) (0)) )) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m2v * (coef_Znth (i) (c2) (0)) )) ”
).

Definition generate_new_constr_safety_wit_24_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX) ”
.

Definition generate_new_constr_safety_wit_24_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((INT_MIN) <= (m2v * (coef_Znth (i) (c2) (0)) )) ”
.

Definition generate_new_constr_safety_wit_25 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m1v * (coef_Znth (i) (c1) (0)) )) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m1v * (coef_Znth (i) (c1) (0)) )) ”
).

Definition generate_new_constr_safety_wit_25_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX) ”
.

Definition generate_new_constr_safety_wit_25_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((INT_MIN) <= (m1v * (coef_Znth (i) (c1) (0)) )) ”
.

Definition generate_new_constr_safety_wit_26 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 0)) (PreH3 : (i_2 <= num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= (num_pre + 1 ))) (PreH8 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH9 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH10 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 )) (PreH11 : (res <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH13 : (retval_2 <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) l )) (PreH15 : (i > num_pre)) (PreH16 : (m1v > 0)) (PreH17 : (m2v > 0)) (PreH18 : (0 <= i)) (PreH19 : (i <= (num_pre + 1 ))) (PreH20 : (ub1 = (INT_MAX ÷ m1v ))) (PreH21 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH22 : (ub2 = (INT_MAX ÷ m2v ))) (PreH23 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH24 : (in_int_range i m1v c1 )) (PreH25 : (in_int_range i m2v c2 )) (PreH26 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH27 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH28 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH29 : (1 <= cur_num_pre)) (PreH30 : (cur_num_pre < (num_pre + 1 ))) (PreH31 : ((num_pre + 1 ) <= INT_MAX)) (PreH32 : (r1_pre <> 0)) (PreH33 : (r2_pre <> 0)) (PreH34 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH35 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH36 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH37 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i_2) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i_2) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ False ”
.

Definition generate_new_constr_safety_wit_27 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 1)) (PreH3 : ((-INT_MAX) <= ((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ))) (PreH4 : (((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX)) (PreH5 : (i_2 <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 <= (num_pre + 1 ))) (PreH10 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH11 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH12 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 )) (PreH13 : (res <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH15 : (retval_2 <> 0)) (PreH16 : (abs_in_int_range (num_pre + 1 ) l )) (PreH17 : (i > num_pre)) (PreH18 : (m1v > 0)) (PreH19 : (m2v > 0)) (PreH20 : (0 <= i)) (PreH21 : (i <= (num_pre + 1 ))) (PreH22 : (ub1 = (INT_MAX ÷ m1v ))) (PreH23 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH24 : (ub2 = (INT_MAX ÷ m2v ))) (PreH25 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH26 : (in_int_range i m1v c1 )) (PreH27 : (in_int_range i m2v c2 )) (PreH28 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH29 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH30 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < (num_pre + 1 ))) (PreH33 : ((num_pre + 1 ) <= INT_MAX)) (PreH34 : (r1_pre <> 0)) (PreH35 : (r2_pre <> 0)) (PreH36 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH37 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH38 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH39 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i_2) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i_2) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ False ”
.

Definition generate_new_constr_safety_wit_28 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 0)) (PreH3 : (i_2 <= num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= (num_pre + 1 ))) (PreH8 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH9 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH10 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 )) (PreH11 : (res <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH13 : (retval_2 <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) l )) (PreH15 : (i > num_pre)) (PreH16 : (m1v > 0)) (PreH17 : (m2v > 0)) (PreH18 : (0 <= i)) (PreH19 : (i <= (num_pre + 1 ))) (PreH20 : (ub1 = (INT_MAX ÷ m1v ))) (PreH21 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH22 : (ub2 = (INT_MAX ÷ m2v ))) (PreH23 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH24 : (in_int_range i m1v c1 )) (PreH25 : (in_int_range i m2v c2 )) (PreH26 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH27 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH28 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH29 : (1 <= cur_num_pre)) (PreH30 : (cur_num_pre < (num_pre + 1 ))) (PreH31 : ((num_pre + 1 ) <= INT_MAX)) (PreH32 : (r1_pre <> 0)) (PreH33 : (r2_pre <> 0)) (PreH34 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH35 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH36 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH37 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i_2) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i_2) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_29 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 1)) (PreH3 : ((-INT_MAX) <= ((m2v * (coef_Znth (i) (c2) (0)) ) + (m1v * (coef_Znth (i) (c1) (0)) ) ))) (PreH4 : (((m2v * (coef_Znth (i) (c2) (0)) ) + (m1v * (coef_Znth (i) (c1) (0)) ) ) <= INT_MAX)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH11 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH12 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH13 : (res <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH15 : (retval_2 <> 0)) (PreH16 : (abs_in_int_range (num_pre + 1 ) l )) (PreH17 : (i_2 > num_pre)) (PreH18 : (m1v > 0)) (PreH19 : (m2v > 0)) (PreH20 : (0 <= i_2)) (PreH21 : (i_2 <= (num_pre + 1 ))) (PreH22 : (ub1 = (INT_MAX ÷ m1v ))) (PreH23 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH24 : (ub2 = (INT_MAX ÷ m2v ))) (PreH25 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH26 : (in_int_range i_2 m1v c1 )) (PreH27 : (in_int_range i_2 m2v c2 )) (PreH28 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH29 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH30 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < (num_pre + 1 ))) (PreH33 : ((num_pre + 1 ) <= INT_MAX)) (PreH34 : (r1_pre <> 0)) (PreH35 : (r2_pre <> 0)) (PreH36 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH37 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH38 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH39 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ (((m2v * (coef_Znth (i) (c2) (0)) ) + (m1v * (coef_Znth (i) (c1) (0)) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((m2v * (coef_Znth (i) (c2) (0)) ) + (m1v * (coef_Znth (i) (c1) (0)) ) )) ”
.

Definition generate_new_constr_safety_wit_30 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 1)) (PreH3 : ((-INT_MAX) <= ((m2v * (coef_Znth (i) (c2) (0)) ) + (m1v * (coef_Znth (i) (c1) (0)) ) ))) (PreH4 : (((m2v * (coef_Znth (i) (c2) (0)) ) + (m1v * (coef_Znth (i) (c1) (0)) ) ) <= INT_MAX)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH11 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH12 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH13 : (res <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH15 : (retval_2 <> 0)) (PreH16 : (abs_in_int_range (num_pre + 1 ) l )) (PreH17 : (i_2 > num_pre)) (PreH18 : (m1v > 0)) (PreH19 : (m2v > 0)) (PreH20 : (0 <= i_2)) (PreH21 : (i_2 <= (num_pre + 1 ))) (PreH22 : (ub1 = (INT_MAX ÷ m1v ))) (PreH23 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH24 : (ub2 = (INT_MAX ÷ m2v ))) (PreH25 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH26 : (in_int_range i_2 m1v c1 )) (PreH27 : (in_int_range i_2 m2v c2 )) (PreH28 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH29 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH30 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < (num_pre + 1 ))) (PreH33 : ((num_pre + 1 ) <= INT_MAX)) (PreH34 : (r1_pre <> 0)) (PreH35 : (r2_pre <> 0)) (PreH36 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH37 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH38 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH39 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (((res + (i * sizeof(INT)))) # Int  |-> ((m2v * (coef_Znth (i) (c2) (0)) ) + (m1v * (coef_Znth (i) (c1) (0)) ) ))
  **  (coef_array_missing_i_rec res i 0 (num_pre + 1 ) c3 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition generate_new_constr_entail_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (PreH1 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : ((num_pre + 1 ) <= INT_MAX)) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH8 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH9 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH10 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  “ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_entail_wit_2 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (PreH1 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH2 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH3 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : ((num_pre + 1 ) <= INT_MAX)) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) (PreH9 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH10 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH11 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH12 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (num_pre + 1 )) ” 
  &&  “ ((INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ) = (INT_MAX ÷ m1v )) ” 
  &&  “ (((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ) = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ ((INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ) = (INT_MAX ÷ m2v )) ” 
  &&  “ (((-INT_MAX) ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ) = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range 0 m1v c1 ) ” 
  &&  “ (in_int_range 0 m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (PreH1 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH2 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH3 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : ((num_pre + 1 ) <= INT_MAX)) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) (PreH9 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH10 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH11 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH12 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  TT && emp 
|--
  “ (in_int_range 0 m2v c2 ) ” 
  &&  “ (in_int_range 0 m1v c1 ) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (m1v > 0) ”
  &&  emp
).

Definition generate_new_constr_entail_wit_2_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (PreH1 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH2 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH3 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : ((num_pre + 1 ) <= INT_MAX)) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) (PreH9 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH10 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH11 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH12 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (in_int_range 0 m2v c2 )
.

Definition generate_new_constr_entail_wit_2_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (PreH1 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH2 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH3 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : ((num_pre + 1 ) <= INT_MAX)) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) (PreH9 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH10 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH11 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH12 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (in_int_range 0 m1v c1 )
.

Definition generate_new_constr_entail_wit_2_split_goal_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (PreH1 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH2 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH3 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : ((num_pre + 1 ) <= INT_MAX)) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) (PreH9 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH10 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH11 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH12 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (m2v > 0)
.

Definition generate_new_constr_entail_wit_2_split_goal_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (PreH1 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH2 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH3 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : ((num_pre + 1 ) <= INT_MAX)) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) (PreH9 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH10 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH11 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH12 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (m1v > 0)
.

Definition generate_new_constr_entail_wit_3 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) <= ub2)) (PreH2 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH3 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH4 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (ub1 = (INT_MAX ÷ m1v ))) (PreH11 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH12 : (ub2 = (INT_MAX ÷ m2v ))) (PreH13 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH14 : (in_int_range i m1v c1 )) (PreH15 : (in_int_range i m2v c2 )) (PreH16 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH17 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH18 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH19 : (1 <= cur_num_pre)) (PreH20 : (cur_num_pre < (num_pre + 1 ))) (PreH21 : ((num_pre + 1 ) <= INT_MAX)) (PreH22 : (r1_pre <> 0)) (PreH23 : (r2_pre <> 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH25 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH26 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH27 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range (i + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (i + 1 ) m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) <= ub2)) (PreH2 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH3 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH4 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (ub1 = (INT_MAX ÷ m1v ))) (PreH11 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH12 : (ub2 = (INT_MAX ÷ m2v ))) (PreH13 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH14 : (in_int_range i m1v c1 )) (PreH15 : (in_int_range i m2v c2 )) (PreH16 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH17 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH18 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH19 : (1 <= cur_num_pre)) (PreH20 : (cur_num_pre < (num_pre + 1 ))) (PreH21 : ((num_pre + 1 ) <= INT_MAX)) (PreH22 : (r1_pre <> 0)) (PreH23 : (r2_pre <> 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH25 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH26 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH27 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  TT && emp 
|--
  “ (in_int_range (i + 1 ) m2v c2 ) ” 
  &&  “ (in_int_range (i + 1 ) m1v c1 ) ”
  &&  emp
).

Definition generate_new_constr_entail_wit_3_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) <= ub2)) (PreH2 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH3 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH4 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (ub1 = (INT_MAX ÷ m1v ))) (PreH11 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH12 : (ub2 = (INT_MAX ÷ m2v ))) (PreH13 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH14 : (in_int_range i m1v c1 )) (PreH15 : (in_int_range i m2v c2 )) (PreH16 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH17 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH18 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH19 : (1 <= cur_num_pre)) (PreH20 : (cur_num_pre < (num_pre + 1 ))) (PreH21 : ((num_pre + 1 ) <= INT_MAX)) (PreH22 : (r1_pre <> 0)) (PreH23 : (r2_pre <> 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH25 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH26 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH27 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (in_int_range (i + 1 ) m2v c2 )
.

Definition generate_new_constr_entail_wit_3_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) <= ub2)) (PreH2 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH3 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH4 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (ub1 = (INT_MAX ÷ m1v ))) (PreH11 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH12 : (ub2 = (INT_MAX ÷ m2v ))) (PreH13 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH14 : (in_int_range i m1v c1 )) (PreH15 : (in_int_range i m2v c2 )) (PreH16 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH17 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH18 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH19 : (1 <= cur_num_pre)) (PreH20 : (cur_num_pre < (num_pre + 1 ))) (PreH21 : ((num_pre + 1 ) <= INT_MAX)) (PreH22 : (r1_pre <> 0)) (PreH23 : (r2_pre <> 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH25 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH26 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH27 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (in_int_range (i + 1 ) m1v c1 )
.

Definition generate_new_constr_entail_wit_4 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (abs_in_int_range (num_pre + 1 ) l )) (PreH3 : (i > num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array retval_2 (num_pre + 1 ) l )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  EX (c3: Constraint) ,
  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre 0 m1v m2v c1 c2 c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array retval_2 (num_pre + 1 ) c3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (abs_in_int_range (num_pre + 1 ) l )) (PreH3 : (i > num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  TT && emp 
|--
  “ (generate_new_constraint_partial cur_num_pre 0 m1v m2v c1 c2 l ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ”
  &&  emp
).

Definition generate_new_constr_entail_wit_4_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (abs_in_int_range (num_pre + 1 ) l )) (PreH3 : (i > num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (generate_new_constraint_partial cur_num_pre 0 m1v m2v c1 c2 l )
.

Definition generate_new_constr_entail_wit_4_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (abs_in_int_range (num_pre + 1 ) l )) (PreH3 : (i > num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (in_int_range (num_pre + 1 ) m2v c2 )
.

Definition generate_new_constr_entail_wit_4_split_goal_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (abs_in_int_range (num_pre + 1 ) l )) (PreH3 : (i > num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (in_int_range (num_pre + 1 ) m1v c1 )
.

Definition generate_new_constr_entail_wit_5 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 1)) (PreH3 : ((-INT_MAX) <= ((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ))) (PreH4 : (((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX)) (PreH5 : (i_2 <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 <= (num_pre + 1 ))) (PreH10 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH11 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH12 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3_2 )) (PreH13 : (res <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) c3_2 )) (PreH15 : (retval_2 <> 0)) (PreH16 : (abs_in_int_range (num_pre + 1 ) l )) (PreH17 : (i > num_pre)) (PreH18 : (m1v > 0)) (PreH19 : (m2v > 0)) (PreH20 : (0 <= i)) (PreH21 : (i <= (num_pre + 1 ))) (PreH22 : (ub1 = (INT_MAX ÷ m1v ))) (PreH23 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH24 : (ub2 = (INT_MAX ÷ m2v ))) (PreH25 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH26 : (in_int_range i m1v c1 )) (PreH27 : (in_int_range i m2v c2 )) (PreH28 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH29 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH30 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < (num_pre + 1 ))) (PreH33 : ((num_pre + 1 ) <= INT_MAX)) (PreH34 : (r1_pre <> 0)) (PreH35 : (r2_pre <> 0)) (PreH36 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH37 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH38 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH39 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (((res + (i_2 * sizeof(INT)))) # Int  |-> ((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ))
  **  (coef_array_missing_i_rec res i_2 0 (num_pre + 1 ) c3_2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  EX (c3: Constraint) ,
  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre (i_2 + 1 ) m1v m2v c1 c2 c3 ) ” 
  &&  “ (res <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ) >= INT_MIN)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((-INT_MAX) <= ((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ))) (PreH5 : (((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX)) (PreH6 : (i_2 <= num_pre)) (PreH7 : (m1v > 0)) (PreH8 : (m2v > 0)) (PreH9 : (0 <= i_2)) (PreH10 : (i_2 <= (num_pre + 1 ))) (PreH11 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH12 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH13 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3_2 )) (PreH14 : (res <> 0)) (PreH15 : (abs_in_int_range (num_pre + 1 ) c3_2 )) (PreH16 : (retval_2 <> 0)) (PreH17 : (abs_in_int_range (num_pre + 1 ) l )) (PreH18 : (i > num_pre)) (PreH19 : (m1v > 0)) (PreH20 : (m2v > 0)) (PreH21 : (0 <= i)) (PreH22 : (i <= (num_pre + 1 ))) (PreH23 : (ub1 = (INT_MAX ÷ m1v ))) (PreH24 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH25 : (ub2 = (INT_MAX ÷ m2v ))) (PreH26 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH27 : (in_int_range i m1v c1 )) (PreH28 : (in_int_range i m2v c2 )) (PreH29 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH30 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH31 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH32 : (1 <= cur_num_pre)) (PreH33 : (cur_num_pre < (num_pre + 1 ))) (PreH34 : ((num_pre + 1 ) <= INT_MAX)) (PreH35 : (r1_pre <> 0)) (PreH36 : (r2_pre <> 0)) (PreH37 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH38 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH39 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH40 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (((res + (i_2 * sizeof(INT)))) # Int  |-> ((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ))
  **  (coef_array_missing_i_rec res i_2 0 (num_pre + 1 ) c3_2 )
|--
  EX (c3: Constraint) ,
  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre (i_2 + 1 ) m1v m2v c1 c2 c3 ) ” 
  &&  “ (res <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array res (num_pre + 1 ) c3 )
).

Definition generate_new_constr_return_wit_1 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (PreH1 : (i_2 > num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3_2 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3_2 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i)) (PreH17 : (i <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i m1v c1 )) (PreH23 : (in_int_range i m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3_2 )
|--
  EX (c3: Constraint) ,
  “ (res <> 0) ” 
  &&  “ (generate_new_constraint cur_num_pre c1 c2 c3 ) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (PreH1 : (i_2 > num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3_2 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3_2 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i)) (PreH17 : (i <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i m1v c1 )) (PreH23 : (in_int_range i m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  TT && emp 
|--
  “ (generate_new_constraint cur_num_pre c1 c2 c3_2 ) ”
  &&  emp
).

Definition generate_new_constr_return_wit_1_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (PreH1 : (i_2 > num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3_2 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3_2 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i)) (PreH17 : (i <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i m1v c1 )) (PreH23 : (in_int_range i m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (generate_new_constraint cur_num_pre c1 c2 c3_2 )
.

Definition generate_new_constr_return_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 0)) (PreH3 : (i_2 <= num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= (num_pre + 1 ))) (PreH8 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH9 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH10 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3_2 )) (PreH11 : (res <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) c3_2 )) (PreH13 : (retval_2 <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) l )) (PreH15 : (i > num_pre)) (PreH16 : (m1v > 0)) (PreH17 : (m2v > 0)) (PreH18 : (0 <= i)) (PreH19 : (i <= (num_pre + 1 ))) (PreH20 : (ub1 = (INT_MAX ÷ m1v ))) (PreH21 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH22 : (ub2 = (INT_MAX ÷ m2v ))) (PreH23 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH24 : (in_int_range i m1v c1 )) (PreH25 : (in_int_range i m2v c2 )) (PreH26 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH27 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH28 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH29 : (1 <= cur_num_pre)) (PreH30 : (cur_num_pre < (num_pre + 1 ))) (PreH31 : ((num_pre + 1 ) <= INT_MAX)) (PreH32 : (r1_pre <> 0)) (PreH33 : (r2_pre <> 0)) (PreH34 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH35 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH36 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH37 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ (0 = 0) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_return_wit_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) < lb2)) (PreH2 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH3 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH4 : (i <= num_pre)) (PreH5 : (m1v > 0)) (PreH6 : (m2v > 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (num_pre + 1 ))) (PreH9 : (ub1 = (INT_MAX ÷ m1v ))) (PreH10 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH11 : (ub2 = (INT_MAX ÷ m2v ))) (PreH12 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH13 : (in_int_range i m1v c1 )) (PreH14 : (in_int_range i m2v c2 )) (PreH15 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH16 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH17 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH18 : (1 <= cur_num_pre)) (PreH19 : (cur_num_pre < (num_pre + 1 ))) (PreH20 : ((num_pre + 1 ) <= INT_MAX)) (PreH21 : (r1_pre <> 0)) (PreH22 : (r2_pre <> 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH25 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH26 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  “ (0 = 0) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_return_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) > ub2)) (PreH2 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH3 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH4 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH5 : (i <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (ub1 = (INT_MAX ÷ m1v ))) (PreH11 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH12 : (ub2 = (INT_MAX ÷ m2v ))) (PreH13 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH14 : (in_int_range i m1v c1 )) (PreH15 : (in_int_range i m2v c2 )) (PreH16 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH17 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH18 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH19 : (1 <= cur_num_pre)) (PreH20 : (cur_num_pre < (num_pre + 1 ))) (PreH21 : ((num_pre + 1 ) <= INT_MAX)) (PreH22 : (r1_pre <> 0)) (PreH23 : (r2_pre <> 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH25 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH26 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH27 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  “ (0 = 0) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_return_wit_5 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c1) (0)) < lb1)) (PreH2 : (i <= num_pre)) (PreH3 : (m1v > 0)) (PreH4 : (m2v > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (num_pre + 1 ))) (PreH7 : (ub1 = (INT_MAX ÷ m1v ))) (PreH8 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH9 : (ub2 = (INT_MAX ÷ m2v ))) (PreH10 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH11 : (in_int_range i m1v c1 )) (PreH12 : (in_int_range i m2v c2 )) (PreH13 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH14 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH15 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH16 : (1 <= cur_num_pre)) (PreH17 : (cur_num_pre < (num_pre + 1 ))) (PreH18 : ((num_pre + 1 ) <= INT_MAX)) (PreH19 : (r1_pre <> 0)) (PreH20 : (r2_pre <> 0)) (PreH21 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH23 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH24 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ (0 = 0) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_return_wit_6 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c1) (0)) > ub1)) (PreH2 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH3 : (i <= num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ (0 = 0) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (PreH1 : (1 <= cur_num_pre)) (PreH2 : (cur_num_pre < (num_pre + 1 ))) (PreH3 : ((num_pre + 1 ) <= INT_MAX)) (PreH4 : (r1_pre <> 0)) (PreH5 : (r2_pre <> 0)) (PreH6 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH8 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH9 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r1_pre + (cur_num_pre * sizeof(INT)))) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre cur_num_pre 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (PreH1 : (1 <= cur_num_pre)) (PreH2 : (cur_num_pre < (num_pre + 1 ))) (PreH3 : ((num_pre + 1 ) <= INT_MAX)) (PreH4 : (r1_pre <> 0)) (PreH5 : (r2_pre <> 0)) (PreH6 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH8 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH9 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r2_pre + (cur_num_pre * sizeof(INT)))) # Int  |-> (coef_Znth (cur_num_pre) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre cur_num_pre 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_3_pure := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (PreH1 : (1 <= cur_num_pre)) (PreH2 : (cur_num_pre < (num_pre + 1 ))) (PreH3 : ((num_pre + 1 ) <= INT_MAX)) (PreH4 : (r1_pre <> 0)) (PreH5 : (r2_pre <> 0)) (PreH6 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH8 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH9 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  “ (0 < (coef_Znth (cur_num_pre) (c1) (0))) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ (0 <= (-(coef_Znth (cur_num_pre) (c2) (0)))) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
.

Definition generate_new_constr_partial_solve_wit_3_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (PreH1 : (1 <= cur_num_pre)) (PreH2 : (cur_num_pre < (num_pre + 1 ))) (PreH3 : ((num_pre + 1 ) <= INT_MAX)) (PreH4 : (r1_pre <> 0)) (PreH5 : (r2_pre <> 0)) (PreH6 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH7 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH8 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH9 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  “ (0 < (coef_Znth (cur_num_pre) (c1) (0))) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ (0 <= (-(coef_Znth (cur_num_pre) (c2) (0)))) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_3 := generate_new_constr_partial_solve_wit_3_pure -> generate_new_constr_partial_solve_wit_3_aux.

Definition generate_new_constr_partial_solve_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (ub1 = (INT_MAX ÷ m1v ))) (PreH7 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH8 : (ub2 = (INT_MAX ÷ m2v ))) (PreH9 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH10 : (in_int_range i m1v c1 )) (PreH11 : (in_int_range i m2v c2 )) (PreH12 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH13 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH14 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH15 : (1 <= cur_num_pre)) (PreH16 : (cur_num_pre < (num_pre + 1 ))) (PreH17 : ((num_pre + 1 ) <= INT_MAX)) (PreH18 : (r1_pre <> 0)) (PreH19 : (r2_pre <> 0)) (PreH20 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH21 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH22 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH23 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ (i <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r1_pre + (i * sizeof(INT)))) # Int  |-> (coef_Znth (i) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre i 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_5 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH2 : (i <= num_pre)) (PreH3 : (m1v > 0)) (PreH4 : (m2v > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (num_pre + 1 ))) (PreH7 : (ub1 = (INT_MAX ÷ m1v ))) (PreH8 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH9 : (ub2 = (INT_MAX ÷ m2v ))) (PreH10 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH11 : (in_int_range i m1v c1 )) (PreH12 : (in_int_range i m2v c2 )) (PreH13 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH14 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH15 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH16 : (1 <= cur_num_pre)) (PreH17 : (cur_num_pre < (num_pre + 1 ))) (PreH18 : ((num_pre + 1 ) <= INT_MAX)) (PreH19 : (r1_pre <> 0)) (PreH20 : (r2_pre <> 0)) (PreH21 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH23 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH24 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ ((coef_Znth (i) (c1) (0)) >= lb1) ” 
  &&  “ (i <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r1_pre + (i * sizeof(INT)))) # Int  |-> (coef_Znth (i) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre i 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_6 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH2 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH3 : (i <= num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (num_pre + 1 ))) (PreH8 : (ub1 = (INT_MAX ÷ m1v ))) (PreH9 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH10 : (ub2 = (INT_MAX ÷ m2v ))) (PreH11 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH12 : (in_int_range i m1v c1 )) (PreH13 : (in_int_range i m2v c2 )) (PreH14 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH15 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH16 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < (num_pre + 1 ))) (PreH19 : ((num_pre + 1 ) <= INT_MAX)) (PreH20 : (r1_pre <> 0)) (PreH21 : (r2_pre <> 0)) (PreH22 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH24 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH25 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ ((coef_Znth (i) (c1) (0)) <= ub1) ” 
  &&  “ ((coef_Znth (i) (c1) (0)) >= lb1) ” 
  &&  “ (i <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r2_pre + (i * sizeof(INT)))) # Int  |-> (coef_Znth (i) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre i 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_7 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : ((coef_Znth (i) (c2) (0)) >= lb2)) (PreH2 : ((coef_Znth (i) (c1) (0)) <= ub1)) (PreH3 : ((coef_Znth (i) (c1) (0)) >= lb1)) (PreH4 : (i <= num_pre)) (PreH5 : (m1v > 0)) (PreH6 : (m2v > 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (num_pre + 1 ))) (PreH9 : (ub1 = (INT_MAX ÷ m1v ))) (PreH10 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH11 : (ub2 = (INT_MAX ÷ m2v ))) (PreH12 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH13 : (in_int_range i m1v c1 )) (PreH14 : (in_int_range i m2v c2 )) (PreH15 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH16 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH17 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH18 : (1 <= cur_num_pre)) (PreH19 : (cur_num_pre < (num_pre + 1 ))) (PreH20 : ((num_pre + 1 ) <= INT_MAX)) (PreH21 : (r1_pre <> 0)) (PreH22 : (r2_pre <> 0)) (PreH23 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH24 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH25 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH26 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  “ ((coef_Znth (i) (c2) (0)) >= lb2) ” 
  &&  “ ((coef_Znth (i) (c1) (0)) <= ub1) ” 
  &&  “ ((coef_Znth (i) (c1) (0)) >= lb1) ” 
  &&  “ (i <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r2_pre + (i * sizeof(INT)))) # Int  |-> (coef_Znth (i) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre i 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_8 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (PreH1 : (i > num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (ub1 = (INT_MAX ÷ m1v ))) (PreH7 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH8 : (ub2 = (INT_MAX ÷ m2v ))) (PreH9 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH10 : (in_int_range i m1v c1 )) (PreH11 : (in_int_range i m2v c2 )) (PreH12 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH13 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH14 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH15 : (1 <= cur_num_pre)) (PreH16 : (cur_num_pre < (num_pre + 1 ))) (PreH17 : ((num_pre + 1 ) <= INT_MAX)) (PreH18 : (r1_pre <> 0)) (PreH19 : (r2_pre <> 0)) (PreH20 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH21 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH22 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH23 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_9 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (PreH1 : (i_2 <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i)) (PreH17 : (i <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i m1v c1 )) (PreH23 : (in_int_range i m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  “ (i_2 <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 ) ” 
  &&  “ (res <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r2_pre + (i_2 * sizeof(INT)))) # Int  |-> (coef_Znth (i_2) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre i_2 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_10 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (PreH1 : (i_2 <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i)) (PreH17 : (i <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i m1v c1 )) (PreH23 : (in_int_range i m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  “ (i_2 <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 ) ” 
  &&  “ (res <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((r1_pre + (i_2 * sizeof(INT)))) # Int  |-> (coef_Znth (i_2) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre i_2 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_11_pure := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (m1v * (coef_Znth (i) (c1) (0)) )) ” 
  &&  “ ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (m2v * (coef_Znth (i) (c2) (0)) )) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (lb2 <= INT_MAX)) (PreH3 : (ub2 <= INT_MAX)) (PreH4 : (lb1 <= INT_MAX)) (PreH5 : (ub1 <= INT_MAX)) (PreH6 : (cur_num_pre <= INT_MAX)) (PreH7 : (num_pre <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (m2v <= INT_MAX)) (PreH10 : (m1v <= INT_MAX)) (PreH11 : ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX)) (PreH12 : ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX)) (PreH13 : ((coef_Znth (cur_num_pre) (c1) (0)) >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : ((-(coef_Znth (cur_num_pre) (c2) (0))) >= INT_MIN)) (PreH16 : (lb2 >= INT_MIN)) (PreH17 : (ub2 >= INT_MIN)) (PreH18 : (lb1 >= INT_MIN)) (PreH19 : (ub1 >= INT_MIN)) (PreH20 : (cur_num_pre >= INT_MIN)) (PreH21 : (num_pre >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (m2v >= INT_MIN)) (PreH24 : (m1v >= INT_MIN)) (PreH25 : ((m2v * (coef_Znth (i) (c2) (0)) ) >= INT_MIN)) (PreH26 : ((m1v * (coef_Znth (i) (c1) (0)) ) >= INT_MIN)) (PreH27 : (i <= num_pre)) (PreH28 : (m1v > 0)) (PreH29 : (m2v > 0)) (PreH30 : (0 <= i)) (PreH31 : (i <= (num_pre + 1 ))) (PreH32 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH33 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH34 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH35 : (res <> 0)) (PreH36 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH37 : (retval_2 <> 0)) (PreH38 : (abs_in_int_range (num_pre + 1 ) l )) (PreH39 : (i_2 > num_pre)) (PreH40 : (m1v > 0)) (PreH41 : (m2v > 0)) (PreH42 : (0 <= i_2)) (PreH43 : (i_2 <= (num_pre + 1 ))) (PreH44 : (ub1 = (INT_MAX ÷ m1v ))) (PreH45 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH46 : (ub2 = (INT_MAX ÷ m2v ))) (PreH47 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH48 : (in_int_range i_2 m1v c1 )) (PreH49 : (in_int_range i_2 m2v c2 )) (PreH50 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH51 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH52 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH53 : (1 <= cur_num_pre)) (PreH54 : (cur_num_pre < (num_pre + 1 ))) (PreH55 : ((num_pre + 1 ) <= INT_MAX)) (PreH56 : (r1_pre <> 0)) (PreH57 : (r2_pre <> 0)) (PreH58 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH59 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH60 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH61 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((-INT_MAX) <= (m2v * (coef_Znth (i) (c2) (0)) )) ” 
  &&  “ ((-INT_MAX) <= (m1v * (coef_Znth (i) (c1) (0)) )) ”
).

Definition generate_new_constr_partial_solve_wit_11_pure_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (lb2 <= INT_MAX)) (PreH3 : (ub2 <= INT_MAX)) (PreH4 : (lb1 <= INT_MAX)) (PreH5 : (ub1 <= INT_MAX)) (PreH6 : (cur_num_pre <= INT_MAX)) (PreH7 : (num_pre <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (m2v <= INT_MAX)) (PreH10 : (m1v <= INT_MAX)) (PreH11 : ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX)) (PreH12 : ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX)) (PreH13 : ((coef_Znth (cur_num_pre) (c1) (0)) >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : ((-(coef_Znth (cur_num_pre) (c2) (0))) >= INT_MIN)) (PreH16 : (lb2 >= INT_MIN)) (PreH17 : (ub2 >= INT_MIN)) (PreH18 : (lb1 >= INT_MIN)) (PreH19 : (ub1 >= INT_MIN)) (PreH20 : (cur_num_pre >= INT_MIN)) (PreH21 : (num_pre >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (m2v >= INT_MIN)) (PreH24 : (m1v >= INT_MIN)) (PreH25 : ((m2v * (coef_Znth (i) (c2) (0)) ) >= INT_MIN)) (PreH26 : ((m1v * (coef_Znth (i) (c1) (0)) ) >= INT_MIN)) (PreH27 : (i <= num_pre)) (PreH28 : (m1v > 0)) (PreH29 : (m2v > 0)) (PreH30 : (0 <= i)) (PreH31 : (i <= (num_pre + 1 ))) (PreH32 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH33 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH34 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH35 : (res <> 0)) (PreH36 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH37 : (retval_2 <> 0)) (PreH38 : (abs_in_int_range (num_pre + 1 ) l )) (PreH39 : (i_2 > num_pre)) (PreH40 : (m1v > 0)) (PreH41 : (m2v > 0)) (PreH42 : (0 <= i_2)) (PreH43 : (i_2 <= (num_pre + 1 ))) (PreH44 : (ub1 = (INT_MAX ÷ m1v ))) (PreH45 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH46 : (ub2 = (INT_MAX ÷ m2v ))) (PreH47 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH48 : (in_int_range i_2 m1v c1 )) (PreH49 : (in_int_range i_2 m2v c2 )) (PreH50 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH51 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH52 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH53 : (1 <= cur_num_pre)) (PreH54 : (cur_num_pre < (num_pre + 1 ))) (PreH55 : ((num_pre + 1 ) <= INT_MAX)) (PreH56 : (r1_pre <> 0)) (PreH57 : (r2_pre <> 0)) (PreH58 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH59 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH60 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH61 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((-INT_MAX) <= (m2v * (coef_Znth (i) (c2) (0)) )) ”
.

Definition generate_new_constr_partial_solve_wit_11_pure_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (lb2 <= INT_MAX)) (PreH3 : (ub2 <= INT_MAX)) (PreH4 : (lb1 <= INT_MAX)) (PreH5 : (ub1 <= INT_MAX)) (PreH6 : (cur_num_pre <= INT_MAX)) (PreH7 : (num_pre <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (m2v <= INT_MAX)) (PreH10 : (m1v <= INT_MAX)) (PreH11 : ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX)) (PreH12 : ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX)) (PreH13 : ((coef_Znth (cur_num_pre) (c1) (0)) >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : ((-(coef_Znth (cur_num_pre) (c2) (0))) >= INT_MIN)) (PreH16 : (lb2 >= INT_MIN)) (PreH17 : (ub2 >= INT_MIN)) (PreH18 : (lb1 >= INT_MIN)) (PreH19 : (ub1 >= INT_MIN)) (PreH20 : (cur_num_pre >= INT_MIN)) (PreH21 : (num_pre >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (m2v >= INT_MIN)) (PreH24 : (m1v >= INT_MIN)) (PreH25 : ((m2v * (coef_Znth (i) (c2) (0)) ) >= INT_MIN)) (PreH26 : ((m1v * (coef_Znth (i) (c1) (0)) ) >= INT_MIN)) (PreH27 : (i <= num_pre)) (PreH28 : (m1v > 0)) (PreH29 : (m2v > 0)) (PreH30 : (0 <= i)) (PreH31 : (i <= (num_pre + 1 ))) (PreH32 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH33 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH34 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH35 : (res <> 0)) (PreH36 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH37 : (retval_2 <> 0)) (PreH38 : (abs_in_int_range (num_pre + 1 ) l )) (PreH39 : (i_2 > num_pre)) (PreH40 : (m1v > 0)) (PreH41 : (m2v > 0)) (PreH42 : (0 <= i_2)) (PreH43 : (i_2 <= (num_pre + 1 ))) (PreH44 : (ub1 = (INT_MAX ÷ m1v ))) (PreH45 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH46 : (ub2 = (INT_MAX ÷ m2v ))) (PreH47 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH48 : (in_int_range i_2 m1v c1 )) (PreH49 : (in_int_range i_2 m2v c2 )) (PreH50 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH51 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH52 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH53 : (1 <= cur_num_pre)) (PreH54 : (cur_num_pre < (num_pre + 1 ))) (PreH55 : ((num_pre + 1 ) <= INT_MAX)) (PreH56 : (r1_pre <> 0)) (PreH57 : (r2_pre <> 0)) (PreH58 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH59 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH60 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH61 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1v * (coef_Znth (i) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2v * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1v)
  **  ((( &( "m2" ) )) # Int  |-> m2v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  “ ((-INT_MAX) <= (m1v * (coef_Znth (i) (c1) (0)) )) ”
.

Definition generate_new_constr_partial_solve_wit_11_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (PreH1 : (i <= num_pre)) (PreH2 : (m1v > 0)) (PreH3 : (m2v > 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (num_pre + 1 ))) (PreH6 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH7 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH8 : (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 )) (PreH9 : (res <> 0)) (PreH10 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH11 : (retval_2 <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) l )) (PreH13 : (i_2 > num_pre)) (PreH14 : (m1v > 0)) (PreH15 : (m2v > 0)) (PreH16 : (0 <= i_2)) (PreH17 : (i_2 <= (num_pre + 1 ))) (PreH18 : (ub1 = (INT_MAX ÷ m1v ))) (PreH19 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH20 : (ub2 = (INT_MAX ÷ m2v ))) (PreH21 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH22 : (in_int_range i_2 m1v c1 )) (PreH23 : (in_int_range i_2 m2v c2 )) (PreH24 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH25 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH26 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < (num_pre + 1 ))) (PreH29 : ((num_pre + 1 ) <= INT_MAX)) (PreH30 : (r1_pre <> 0)) (PreH31 : (r2_pre <> 0)) (PreH32 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH33 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH34 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH35 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  “ ((m1v * (coef_Znth (i) (c1) (0)) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (m1v * (coef_Znth (i) (c1) (0)) )) ” 
  &&  “ ((m2v * (coef_Znth (i) (c2) (0)) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (m2v * (coef_Znth (i) (c2) (0)) )) ” 
  &&  “ (i <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre i m1v m2v c1 c2 c3 ) ” 
  &&  “ (res <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i_2 > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i_2 m1v c1 ) ” 
  &&  “ (in_int_range i_2 m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_11 := generate_new_constr_partial_solve_wit_11_pure -> generate_new_constr_partial_solve_wit_11_aux.

Definition generate_new_constr_partial_solve_wit_12 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 0)) (PreH3 : (i_2 <= num_pre)) (PreH4 : (m1v > 0)) (PreH5 : (m2v > 0)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= (num_pre + 1 ))) (PreH8 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH9 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH10 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 )) (PreH11 : (res <> 0)) (PreH12 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH13 : (retval_2 <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) l )) (PreH15 : (i > num_pre)) (PreH16 : (m1v > 0)) (PreH17 : (m2v > 0)) (PreH18 : (0 <= i)) (PreH19 : (i <= (num_pre + 1 ))) (PreH20 : (ub1 = (INT_MAX ÷ m1v ))) (PreH21 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH22 : (ub2 = (INT_MAX ÷ m2v ))) (PreH23 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH24 : (in_int_range i m1v c1 )) (PreH25 : (in_int_range i m2v c2 )) (PreH26 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH27 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH28 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH29 : (1 <= cur_num_pre)) (PreH30 : (cur_num_pre < (num_pre + 1 ))) (PreH31 : ((num_pre + 1 ) <= INT_MAX)) (PreH32 : (r1_pre <> 0)) (PreH33 : (r2_pre <> 0)) (PreH34 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH35 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH36 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH37 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  “ (retval_3 = 0) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (i_2 <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 ) ” 
  &&  “ (res <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (coef_array res (num_pre + 1 ) c3 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_13 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (m1v: Z) (m2v: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 1)) (PreH3 : ((-INT_MAX) <= ((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ))) (PreH4 : (((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX)) (PreH5 : (i_2 <= num_pre)) (PreH6 : (m1v > 0)) (PreH7 : (m2v > 0)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 <= (num_pre + 1 ))) (PreH10 : (in_int_range (num_pre + 1 ) m1v c1 )) (PreH11 : (in_int_range (num_pre + 1 ) m2v c2 )) (PreH12 : (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 )) (PreH13 : (res <> 0)) (PreH14 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH15 : (retval_2 <> 0)) (PreH16 : (abs_in_int_range (num_pre + 1 ) l )) (PreH17 : (i > num_pre)) (PreH18 : (m1v > 0)) (PreH19 : (m2v > 0)) (PreH20 : (0 <= i)) (PreH21 : (i <= (num_pre + 1 ))) (PreH22 : (ub1 = (INT_MAX ÷ m1v ))) (PreH23 : (lb1 = ((-INT_MAX) ÷ m1v ))) (PreH24 : (ub2 = (INT_MAX ÷ m2v ))) (PreH25 : (lb2 = ((-INT_MAX) ÷ m2v ))) (PreH26 : (in_int_range i m1v c1 )) (PreH27 : (in_int_range i m2v c2 )) (PreH28 : (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))) (PreH29 : (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))) (PreH30 : (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0))))))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < (num_pre + 1 ))) (PreH33 : ((num_pre + 1 ) <= INT_MAX)) (PreH34 : (r1_pre <> 0)) (PreH35 : (r2_pre <> 0)) (PreH36 : ((coef_Znth (cur_num_pre) (c1) (0)) > 0)) (PreH37 : ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX)) (PreH38 : ((coef_Znth (cur_num_pre) (c2) (0)) < 0)) (PreH39 : ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX)) ,
  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((-INT_MAX) <= ((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) )) ” 
  &&  “ (((m2v * (coef_Znth (i_2) (c2) (0)) ) + (m1v * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX) ” 
  &&  “ (i_2 <= num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= (num_pre + 1 )) ” 
  &&  “ (in_int_range (num_pre + 1 ) m1v c1 ) ” 
  &&  “ (in_int_range (num_pre + 1 ) m2v c2 ) ” 
  &&  “ (generate_new_constraint_partial cur_num_pre i_2 m1v m2v c1 c2 c3 ) ” 
  &&  “ (res <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) l ) ” 
  &&  “ (i > num_pre) ” 
  &&  “ (m1v > 0) ” 
  &&  “ (m2v > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (ub1 = (INT_MAX ÷ m1v )) ” 
  &&  “ (lb1 = ((-INT_MAX) ÷ m1v )) ” 
  &&  “ (ub2 = (INT_MAX ÷ m2v )) ” 
  &&  “ (lb2 = ((-INT_MAX) ÷ m2v )) ” 
  &&  “ (in_int_range i m1v c1 ) ” 
  &&  “ (in_int_range i m2v c2 ) ” 
  &&  “ (m1v = ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval )) ” 
  &&  “ (m2v = ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval )) ” 
  &&  “ (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) ”
  &&  (((res + (i_2 * sizeof(INT)))) # Int  |->_)
  **  (coef_array_missing_i_rec res i_2 0 (num_pre + 1 ) c3 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

(*----- Function generate_new_constraint_list -----*)

Definition generate_new_constraint_list_safety_wit_1 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (PreH1 : (n = (num_pre + 1 ))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < n)) (PreH4 : (InequList_nth_pos cur_num_pre l1 )) (PreH5 : (InequList_nth_neg cur_num_pre l2 )) (PreH6 : (l1 = (app (l11) (l12)))) (PreH7 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH8 : (l3 = (app (l4) (l_init)))) (PreH9 : (LP_abs_in_int_range n l3 )) (PreH10 : (n = (num_pre + 1 ))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < n)) (PreH13 : (n <= INT_MAX)) (PreH14 : (InequList_nth_pos cur_num_pre l1 )) (PreH15 : (InequList_nth_neg cur_num_pre l2 )) (PreH16 : (LP_abs_in_int_range n l1 )) (PreH17 : (LP_abs_in_int_range n l2 )) (PreH18 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constraint_list_safety_wit_2 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (PreH1 : (n = (num_pre + 1 ))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < n)) (PreH4 : (InequList_nth_pos cur_num_pre l1 )) (PreH5 : (InequList_nth_neg cur_num_pre l2 )) (PreH6 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH7 : (l2 = (app (l21) (l22)))) (PreH8 : (p1_2 <> 0)) (PreH9 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH10 : (l3_2 = (app (l4_2) (l_init)))) (PreH11 : (LP_abs_in_int_range n l3_2 )) (PreH12 : (p1_coef_2 <> 0)) (PreH13 : (l12 = (cons (x) (l13)))) (PreH14 : (p1_coef <> 0)) (PreH15 : (p1 <> 0)) (PreH16 : (n = (num_pre + 1 ))) (PreH17 : (1 <= cur_num_pre)) (PreH18 : (cur_num_pre < n)) (PreH19 : (InequList_nth_pos cur_num_pre l1 )) (PreH20 : (InequList_nth_neg cur_num_pre l2 )) (PreH21 : (l1 = (app (l11) (l12)))) (PreH22 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH23 : (l3 = (app (l4) (l_init)))) (PreH24 : (LP_abs_in_int_range n l3 )) (PreH25 : (n = (num_pre + 1 ))) (PreH26 : (1 <= cur_num_pre)) (PreH27 : (cur_num_pre < n)) (PreH28 : (n <= INT_MAX)) (PreH29 : (InequList_nth_pos cur_num_pre l1 )) (PreH30 : (InequList_nth_neg cur_num_pre l2 )) (PreH31 : (LP_abs_in_int_range n l1 )) (PreH32 : (LP_abs_in_int_range n l2 )) (PreH33 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constraint_list_safety_wit_3 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraint cur_num_pre x1 x_2 c3 )) (PreH3 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH4 : (l22 = (cons (x_2) (l23)))) (PreH5 : (p2_coef <> 0)) (PreH6 : (p2 <> 0)) (PreH7 : (n = (num_pre + 1 ))) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < n)) (PreH10 : (InequList_nth_pos cur_num_pre l1 )) (PreH11 : (InequList_nth_neg cur_num_pre l2 )) (PreH12 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH13 : (l2 = (app (l21) (l22)))) (PreH14 : (p1_2 <> 0)) (PreH15 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH16 : (l3_2 = (app (l4_2) (l_init)))) (PreH17 : (LP_abs_in_int_range n l3_2 )) (PreH18 : (p1_coef_2 <> 0)) (PreH19 : (l12 = (cons (x) (l13)))) (PreH20 : (p1_coef <> 0)) (PreH21 : (p1 <> 0)) (PreH22 : (n = (num_pre + 1 ))) (PreH23 : (1 <= cur_num_pre)) (PreH24 : (cur_num_pre < n)) (PreH25 : (InequList_nth_pos cur_num_pre l1 )) (PreH26 : (InequList_nth_neg cur_num_pre l2 )) (PreH27 : (l1 = (app (l11) (l12)))) (PreH28 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH29 : (l3 = (app (l4) (l_init)))) (PreH30 : (LP_abs_in_int_range n l3 )) (PreH31 : (n = (num_pre + 1 ))) (PreH32 : (1 <= cur_num_pre)) (PreH33 : (cur_num_pre < n)) (PreH34 : (n <= INT_MAX)) (PreH35 : (InequList_nth_pos cur_num_pre l1 )) (PreH36 : (InequList_nth_neg cur_num_pre l2 )) (PreH37 : (LP_abs_in_int_range n l1 )) (PreH38 : (LP_abs_in_int_range n l2 )) (PreH39 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (coef_array retval (num_pre + 1 ) c3 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constraint_list_safety_wit_4 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (l22 = (cons (x_2) (l23)))) (PreH3 : (p2_coef <> 0)) (PreH4 : (p2 <> 0)) (PreH5 : (n = (num_pre + 1 ))) (PreH6 : (1 <= cur_num_pre)) (PreH7 : (cur_num_pre < n)) (PreH8 : (InequList_nth_pos cur_num_pre l1 )) (PreH9 : (InequList_nth_neg cur_num_pre l2 )) (PreH10 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH11 : (l2 = (app (l21) (l22)))) (PreH12 : (p1_2 <> 0)) (PreH13 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH14 : (l3_2 = (app (l4_2) (l_init)))) (PreH15 : (LP_abs_in_int_range n l3_2 )) (PreH16 : (p1_coef_2 <> 0)) (PreH17 : (l12 = (cons (x) (l13)))) (PreH18 : (p1_coef <> 0)) (PreH19 : (p1 <> 0)) (PreH20 : (n = (num_pre + 1 ))) (PreH21 : (1 <= cur_num_pre)) (PreH22 : (cur_num_pre < n)) (PreH23 : (InequList_nth_pos cur_num_pre l1 )) (PreH24 : (InequList_nth_neg cur_num_pre l2 )) (PreH25 : (l1 = (app (l11) (l12)))) (PreH26 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH27 : (l3 = (app (l4) (l_init)))) (PreH28 : (LP_abs_in_int_range n l3 )) (PreH29 : (n = (num_pre + 1 ))) (PreH30 : (1 <= cur_num_pre)) (PreH31 : (cur_num_pre < n)) (PreH32 : (n <= INT_MAX)) (PreH33 : (InequList_nth_pos cur_num_pre l1 )) (PreH34 : (InequList_nth_neg cur_num_pre l2 )) (PreH35 : (LP_abs_in_int_range n l1 )) (PreH36 : (LP_abs_in_int_range n l2 )) (PreH37 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constraint_list_safety_wit_5 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (generate_new_constraint cur_num_pre x1 x_2 c3 )) (PreH4 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH5 : (l22 = (cons (x_2) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef_2 <> 0)) (PreH20 : (l12 = (cons (x) (l13)))) (PreH21 : (p1_coef <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (coef_array retval (num_pre + 1 ) c3 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ False ”
.

Definition generate_new_constraint_list_safety_wit_6 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (l22 = (cons (x_2) (l23)))) (PreH4 : (p2_coef <> 0)) (PreH5 : (p2 <> 0)) (PreH6 : (n = (num_pre + 1 ))) (PreH7 : (1 <= cur_num_pre)) (PreH8 : (cur_num_pre < n)) (PreH9 : (InequList_nth_pos cur_num_pre l1 )) (PreH10 : (InequList_nth_neg cur_num_pre l2 )) (PreH11 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH12 : (l2 = (app (l21) (l22)))) (PreH13 : (p1_2 <> 0)) (PreH14 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH15 : (l3_2 = (app (l4_2) (l_init)))) (PreH16 : (LP_abs_in_int_range n l3_2 )) (PreH17 : (p1_coef_2 <> 0)) (PreH18 : (l12 = (cons (x) (l13)))) (PreH19 : (p1_coef <> 0)) (PreH20 : (p1 <> 0)) (PreH21 : (n = (num_pre + 1 ))) (PreH22 : (1 <= cur_num_pre)) (PreH23 : (cur_num_pre < n)) (PreH24 : (InequList_nth_pos cur_num_pre l1 )) (PreH25 : (InequList_nth_neg cur_num_pre l2 )) (PreH26 : (l1 = (app (l11) (l12)))) (PreH27 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH28 : (l3 = (app (l4) (l_init)))) (PreH29 : (LP_abs_in_int_range n l3 )) (PreH30 : (n = (num_pre + 1 ))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < n)) (PreH33 : (n <= INT_MAX)) (PreH34 : (InequList_nth_pos cur_num_pre l1 )) (PreH35 : (InequList_nth_neg cur_num_pre l2 )) (PreH36 : (LP_abs_in_int_range n l1 )) (PreH37 : (LP_abs_in_int_range n l2 )) (PreH38 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ False ”
.

Definition generate_new_constraint_list_safety_wit_7 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (l22 = (cons (x_2) (l23)))) (PreH4 : (p2_coef <> 0)) (PreH5 : (p2 <> 0)) (PreH6 : (n = (num_pre + 1 ))) (PreH7 : (1 <= cur_num_pre)) (PreH8 : (cur_num_pre < n)) (PreH9 : (InequList_nth_pos cur_num_pre l1 )) (PreH10 : (InequList_nth_neg cur_num_pre l2 )) (PreH11 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH12 : (l2 = (app (l21) (l22)))) (PreH13 : (p1_2 <> 0)) (PreH14 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH15 : (l3_2 = (app (l4_2) (l_init)))) (PreH16 : (LP_abs_in_int_range n l3_2 )) (PreH17 : (p1_coef_2 <> 0)) (PreH18 : (l12 = (cons (x) (l13)))) (PreH19 : (p1_coef <> 0)) (PreH20 : (p1 <> 0)) (PreH21 : (n = (num_pre + 1 ))) (PreH22 : (1 <= cur_num_pre)) (PreH23 : (cur_num_pre < n)) (PreH24 : (InequList_nth_pos cur_num_pre l1 )) (PreH25 : (InequList_nth_neg cur_num_pre l2 )) (PreH26 : (l1 = (app (l11) (l12)))) (PreH27 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH28 : (l3 = (app (l4) (l_init)))) (PreH29 : (LP_abs_in_int_range n l3 )) (PreH30 : (n = (num_pre + 1 ))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < n)) (PreH33 : (n <= INT_MAX)) (PreH34 : (InequList_nth_pos cur_num_pre l1 )) (PreH35 : (InequList_nth_neg cur_num_pre l2 )) (PreH36 : (LP_abs_in_int_range n l1 )) (PreH37 : (LP_abs_in_int_range n l2 )) (PreH38 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constraint_list_entail_wit_1 := 
(
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (PreH1 : (n = (num_pre + 1 ))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (LP_abs_in_int_range n l1 )) (PreH8 : (LP_abs_in_int_range n l2 )) (PreH9 : (LP_abs_in_int_range n l_init )) ,
  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 )
  **  (InequList init_pre n l_init )
|--
  EX (l3: (@list Constraint))  (l4: (@list Constraint))  (l11: (@list Constraint))  (l12: (@list Constraint)) ,
  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (InequList_seg r1_pre r1_pre n l11 )
  **  (InequList r1_pre n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList init_pre n l3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (PreH1 : (n = (num_pre + 1 ))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (LP_abs_in_int_range n l1 )) (PreH8 : (LP_abs_in_int_range n l2 )) (PreH9 : (LP_abs_in_int_range n l_init )) ,
  TT && emp 
|--
  EX (l4: (@list Constraint)) ,
  “ (l_init = (app (l4) (l_init))) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app ((@nil Constraint)) (l1))) ” 
  &&  “ (generate_new_constraints cur_num_pre (@nil Constraint) l2 l4 ) ” 
  &&  “ (LP_abs_in_int_range n (app (l4) (l_init)) ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  emp
).

Definition generate_new_constraint_list_entail_wit_2 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_next_2: Z) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (PreH1 : (l12 = (cons (x) (l13)))) (PreH2 : (p1_coef <> 0)) (PreH3 : (p1 <> 0)) (PreH4 : (n = (num_pre + 1 ))) (PreH5 : (1 <= cur_num_pre)) (PreH6 : (cur_num_pre < n)) (PreH7 : (InequList_nth_pos cur_num_pre l1 )) (PreH8 : (InequList_nth_neg cur_num_pre l2 )) (PreH9 : (l1 = (app (l11) (l12)))) (PreH10 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH11 : (l3 = (app (l4) (l_init)))) (PreH12 : (LP_abs_in_int_range n l3 )) (PreH13 : (n = (num_pre + 1 ))) (PreH14 : (1 <= cur_num_pre)) (PreH15 : (cur_num_pre < n)) (PreH16 : (n <= INT_MAX)) (PreH17 : (InequList_nth_pos cur_num_pre l1 )) (PreH18 : (InequList_nth_neg cur_num_pre l2 )) (PreH19 : (LP_abs_in_int_range n l1 )) (PreH20 : (LP_abs_in_int_range n l2 )) (PreH21 : (LP_abs_in_int_range n l_init )) ,
  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1 n l11 )
  **  (coef_array p1_coef n x )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next_2)
  **  (InequList p1_next_2 n l13 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 )
|--
  EX (p1_next: Z)  (p1_coef_2: Z)  (l3_2: (@list Constraint))  (l4_2: (@list Constraint))  (l21: (@list Constraint))  (l22: (@list Constraint))  (l11_2: (@list Constraint))  (x1: Constraint)  (l12_2: (@list Constraint)) ,
  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11_2) ((cons (x1) (l12_2))))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 ) ” 
  &&  “ (l3_2 = (app (l4_2) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3_2 ) ” 
  &&  “ (p1_coef_2 <> 0) ” 
  &&  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1 n l11_2 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList_seg r2_pre r2_pre n l21 )
  **  (InequList r2_pre n l22 )
  **  (InequList res n l3_2 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (PreH1 : (l12 = (cons (x) (l13)))) (PreH2 : (p1_coef <> 0)) (PreH3 : (p1 <> 0)) (PreH4 : (n = (num_pre + 1 ))) (PreH5 : (1 <= cur_num_pre)) (PreH6 : (cur_num_pre < n)) (PreH7 : (InequList_nth_pos cur_num_pre l1 )) (PreH8 : (InequList_nth_neg cur_num_pre l2 )) (PreH9 : (l1 = (app (l11) (l12)))) (PreH10 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH11 : (l3 = (app (l4) (l_init)))) (PreH12 : (LP_abs_in_int_range n l3 )) (PreH13 : (n = (num_pre + 1 ))) (PreH14 : (1 <= cur_num_pre)) (PreH15 : (cur_num_pre < n)) (PreH16 : (n <= INT_MAX)) (PreH17 : (InequList_nth_pos cur_num_pre l1 )) (PreH18 : (InequList_nth_neg cur_num_pre l2 )) (PreH19 : (LP_abs_in_int_range n l1 )) (PreH20 : (LP_abs_in_int_range n l2 )) (PreH21 : (LP_abs_in_int_range n l_init )) ,
  TT && emp 
|--
  EX (l4_2: (@list Constraint)) ,
  “ (l3 = (app (l4_2) (l_init))) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) ((cons (x) (l13))))) ” 
  &&  “ (l2 = (app ((@nil Constraint)) (l2))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11 x (@nil Constraint) l2 l4_2 ) ” 
  &&  “ (LP_abs_in_int_range n (app (l4_2) (l_init)) ) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  emp
).

Definition generate_new_constraint_list_entail_wit_3 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (p2: Z) (p1_next_2: Z) (p1_coef_3: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (p1_2: Z) (l21_2: (@list Constraint)) (l22_2: (@list Constraint)) (l11_3: (@list Constraint)) (x1_2: Constraint) (l12_3: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (generate_new_constraint cur_num_pre x1_2 x_2 c3 )) (PreH4 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH5 : (l22_2 = (cons (x_2) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_3) ((cons (x1_2) (l12_3)))))) (PreH14 : (l2 = (app (l21_2) (l22_2)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_3 x1_2 l21_2 l22_2 l4_3 )) (PreH17 : (l3_3 = (app (l4_3) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_3 )) (PreH19 : (p1_coef_3 <> 0)) (PreH20 : (l12 = (cons (x) (l13)))) (PreH21 : (p1_coef <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  (InequList retval (num_pre + 1 ) (cons (c3) (l3_3)) )
  **  (coef_array p1_coef_3 (num_pre + 1 ) x1_2 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21_2 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_3)
  **  (InequList_seg r1_pre p1_2 n l11_3 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next_2)
  **  (InequList p1_next_2 n l12_3 )
|--
  EX (p1_next: Z)  (p1_coef_2: Z)  (l3_2: (@list Constraint))  (l4_2: (@list Constraint))  (l21: (@list Constraint))  (l22: (@list Constraint))  (l11_2: (@list Constraint))  (x1: Constraint)  (l12_2: (@list Constraint)) ,
  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11_2) ((cons (x1) (l12_2))))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (p1_2 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 ) ” 
  &&  “ (l3_2 = (app (l4_2) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3_2 ) ” 
  &&  “ (p1_coef_2 <> 0) ” 
  &&  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList_seg r2_pre p2_next n l21 )
  **  (InequList p2_next n l22 )
  **  (InequList retval n l3_2 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (p2: Z) (p1_coef_3: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (p1_2: Z) (l21_2: (@list Constraint)) (l22_2: (@list Constraint)) (l11_3: (@list Constraint)) (x1_2: Constraint) (l12_3: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (generate_new_constraint cur_num_pre x1_2 x_2 c3 )) (PreH4 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH5 : (l22_2 = (cons (x_2) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_3) ((cons (x1_2) (l12_3)))))) (PreH14 : (l2 = (app (l21_2) (l22_2)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_3 x1_2 l21_2 l22_2 l4_3 )) (PreH17 : (l3_3 = (app (l4_3) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_3 )) (PreH19 : (p1_coef_3 <> 0)) (PreH20 : (l12 = (cons (x) (l13)))) (PreH21 : (p1_coef <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21_2 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
|--
  EX (l4_2: (@list Constraint))  (l21: (@list Constraint)) ,
  “ ((num_pre + 1 ) = n) ” 
  &&  “ ((cons (c3) (l3_3)) = (app (l4_2) (l_init))) ” 
  &&  “ ((num_pre + 1 ) = n) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11_3) ((cons (x1_2) (l12_3))))) ” 
  &&  “ (l2 = (app (l21) (l23))) ” 
  &&  “ (p1_2 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11_3 x1_2 l21 l23 l4_2 ) ” 
  &&  “ (LP_abs_in_int_range n (app (l4_2) (l_init)) ) ” 
  &&  “ (p1_coef_3 <> 0) ” 
  &&  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (InequList_seg r2_pre p2_next n l21 )
).

Definition generate_new_constraint_list_entail_wit_4 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_3: (@list Constraint)) (x1: Constraint) (l12_3: (@list Constraint)) (PreH1 : (p2 = 0)) (PreH2 : (n = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (l1 = (app (l11_3) ((cons (x1) (l12_3)))))) (PreH8 : (l2 = (app (l21) (l22)))) (PreH9 : (p1_2 <> 0)) (PreH10 : (generate_new_constraints_partial cur_num_pre l11_3 x1 l21 l22 l4_3 )) (PreH11 : (l3_3 = (app (l4_3) (l_init)))) (PreH12 : (LP_abs_in_int_range n l3_3 )) (PreH13 : (p1_coef_2 <> 0)) (PreH14 : (l12_2 = (cons (x) (l13)))) (PreH15 : (p1_coef <> 0)) (PreH16 : (p1 <> 0)) (PreH17 : (n = (num_pre + 1 ))) (PreH18 : (1 <= cur_num_pre)) (PreH19 : (cur_num_pre < n)) (PreH20 : (InequList_nth_pos cur_num_pre l1 )) (PreH21 : (InequList_nth_neg cur_num_pre l2 )) (PreH22 : (l1 = (app (l11_2) (l12_2)))) (PreH23 : (generate_new_constraints cur_num_pre l11_2 l2 l4_2 )) (PreH24 : (l3_2 = (app (l4_2) (l_init)))) (PreH25 : (LP_abs_in_int_range n l3_2 )) (PreH26 : (n = (num_pre + 1 ))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < n)) (PreH29 : (n <= INT_MAX)) (PreH30 : (InequList_nth_pos cur_num_pre l1 )) (PreH31 : (InequList_nth_neg cur_num_pre l2 )) (PreH32 : (LP_abs_in_int_range n l1 )) (PreH33 : (LP_abs_in_int_range n l2 )) (PreH34 : (LP_abs_in_int_range n l_init )) ,
  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_3 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_3 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  (InequList res n l3_3 )
|--
  EX (l3: (@list Constraint))  (l4: (@list Constraint))  (l11: (@list Constraint))  (l12: (@list Constraint)) ,
  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (InequList_seg r1_pre p1_next n l11 )
  **  (InequList p1_next n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_3: (@list Constraint)) (x1: Constraint) (l12_3: (@list Constraint)) (PreH1 : (p2 = 0)) (PreH2 : (n = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (l1 = (app (l11_3) ((cons (x1) (l12_3)))))) (PreH8 : (l2 = (app (l21) (l22)))) (PreH9 : (p1_2 <> 0)) (PreH10 : (generate_new_constraints_partial cur_num_pre l11_3 x1 l21 l22 l4_3 )) (PreH11 : (l3_3 = (app (l4_3) (l_init)))) (PreH12 : (LP_abs_in_int_range n l3_3 )) (PreH13 : (p1_coef_2 <> 0)) (PreH14 : (l12_2 = (cons (x) (l13)))) (PreH15 : (p1_coef <> 0)) (PreH16 : (p1 <> 0)) (PreH17 : (n = (num_pre + 1 ))) (PreH18 : (1 <= cur_num_pre)) (PreH19 : (cur_num_pre < n)) (PreH20 : (InequList_nth_pos cur_num_pre l1 )) (PreH21 : (InequList_nth_neg cur_num_pre l2 )) (PreH22 : (l1 = (app (l11_2) (l12_2)))) (PreH23 : (generate_new_constraints cur_num_pre l11_2 l2 l4_2 )) (PreH24 : (l3_2 = (app (l4_2) (l_init)))) (PreH25 : (LP_abs_in_int_range n l3_2 )) (PreH26 : (n = (num_pre + 1 ))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < n)) (PreH29 : (n <= INT_MAX)) (PreH30 : (InequList_nth_pos cur_num_pre l1 )) (PreH31 : (InequList_nth_neg cur_num_pre l2 )) (PreH32 : (LP_abs_in_int_range n l1 )) (PreH33 : (LP_abs_in_int_range n l2 )) (PreH34 : (LP_abs_in_int_range n l_init )) ,
  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_3 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
|--
  EX (l4: (@list Constraint))  (l11: (@list Constraint)) ,
  “ (l3_3 = (app (l4) (l_init))) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12_3))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (LP_abs_in_int_range n (app (l4) (l_init)) ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (InequList_seg r1_pre p1_next n l11 )
  **  (InequList r2_pre n l2 )
).

Definition generate_new_constraint_list_return_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (PreH1 : (p1 = 0)) (PreH2 : (n = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (l1 = (app (l11) (l12)))) (PreH8 : (generate_new_constraints cur_num_pre l11 l2 l4_2 )) (PreH9 : (l3_2 = (app (l4_2) (l_init)))) (PreH10 : (LP_abs_in_int_range n l3_2 )) (PreH11 : (n = (num_pre + 1 ))) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < n)) (PreH14 : (n <= INT_MAX)) (PreH15 : (InequList_nth_pos cur_num_pre l1 )) (PreH16 : (InequList_nth_neg cur_num_pre l2 )) (PreH17 : (LP_abs_in_int_range n l1 )) (PreH18 : (LP_abs_in_int_range n l2 )) (PreH19 : (LP_abs_in_int_range n l_init )) ,
  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3_2 )
|--
  (“ (res = 0) ”
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 ))
  ||
  (EX (l3: (@list Constraint))  (l4: (@list Constraint)) ,
  “ (generate_new_constraints cur_num_pre l1 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ”
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 ))
.

Definition generate_new_constraint_list_return_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (l22 = (cons (x_2) (l23)))) (PreH4 : (p2_coef <> 0)) (PreH5 : (p2 <> 0)) (PreH6 : (n = (num_pre + 1 ))) (PreH7 : (1 <= cur_num_pre)) (PreH8 : (cur_num_pre < n)) (PreH9 : (InequList_nth_pos cur_num_pre l1 )) (PreH10 : (InequList_nth_neg cur_num_pre l2 )) (PreH11 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH12 : (l2 = (app (l21) (l22)))) (PreH13 : (p1_2 <> 0)) (PreH14 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_3 )) (PreH15 : (l3_3 = (app (l4_3) (l_init)))) (PreH16 : (LP_abs_in_int_range n l3_3 )) (PreH17 : (p1_coef_2 <> 0)) (PreH18 : (l12 = (cons (x) (l13)))) (PreH19 : (p1_coef <> 0)) (PreH20 : (p1 <> 0)) (PreH21 : (n = (num_pre + 1 ))) (PreH22 : (1 <= cur_num_pre)) (PreH23 : (cur_num_pre < n)) (PreH24 : (InequList_nth_pos cur_num_pre l1 )) (PreH25 : (InequList_nth_neg cur_num_pre l2 )) (PreH26 : (l1 = (app (l11) (l12)))) (PreH27 : (generate_new_constraints cur_num_pre l11 l2 l4_2 )) (PreH28 : (l3_2 = (app (l4_2) (l_init)))) (PreH29 : (LP_abs_in_int_range n l3_2 )) (PreH30 : (n = (num_pre + 1 ))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < n)) (PreH33 : (n <= INT_MAX)) (PreH34 : (InequList_nth_pos cur_num_pre l1 )) (PreH35 : (InequList_nth_neg cur_num_pre l2 )) (PreH36 : (LP_abs_in_int_range n l1 )) (PreH37 : (LP_abs_in_int_range n l2 )) (PreH38 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
|--
  (“ (0 = 0) ”
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 ))
  ||
  (EX (l3: (@list Constraint))  (l4: (@list Constraint)) ,
  “ (generate_new_constraints cur_num_pre l1 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ”
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 )
  **  (InequList 0 n l3 ))
.

Definition generate_new_constraint_list_partial_solve_wit_1_pure := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (PreH1 : (p1 <> 0)) (PreH2 : (n = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (l1 = (app (l11) (l12)))) (PreH8 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH9 : (l3 = (app (l4) (l_init)))) (PreH10 : (LP_abs_in_int_range n l3 )) (PreH11 : (n = (num_pre + 1 ))) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < n)) (PreH14 : (n <= INT_MAX)) (PreH15 : (InequList_nth_pos cur_num_pre l1 )) (PreH16 : (InequList_nth_neg cur_num_pre l2 )) (PreH17 : (LP_abs_in_int_range n l1 )) (PreH18 : (LP_abs_in_int_range n l2 )) (PreH19 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3 )
|--
  “ (p1 <> 0) ”
.

Definition generate_new_constraint_list_partial_solve_wit_1_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (PreH1 : (p1 <> 0)) (PreH2 : (n = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (l1 = (app (l11) (l12)))) (PreH8 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH9 : (l3 = (app (l4) (l_init)))) (PreH10 : (LP_abs_in_int_range n l3 )) (PreH11 : (n = (num_pre + 1 ))) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < n)) (PreH14 : (n <= INT_MAX)) (PreH15 : (InequList_nth_pos cur_num_pre l1 )) (PreH16 : (InequList_nth_neg cur_num_pre l2 )) (PreH17 : (LP_abs_in_int_range n l1 )) (PreH18 : (LP_abs_in_int_range n l2 )) (PreH19 : (LP_abs_in_int_range n l_init )) ,
  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 )
|--
  “ (p1 <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 )
.

Definition generate_new_constraint_list_partial_solve_wit_1 := generate_new_constraint_list_partial_solve_wit_1_pure -> generate_new_constraint_list_partial_solve_wit_1_aux.

Definition generate_new_constraint_list_partial_solve_wit_2_pure := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (PreH1 : (p2 <> 0)) (PreH2 : (n = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH8 : (l2 = (app (l21) (l22)))) (PreH9 : (p1_2 <> 0)) (PreH10 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH11 : (l3_2 = (app (l4_2) (l_init)))) (PreH12 : (LP_abs_in_int_range n l3_2 )) (PreH13 : (p1_coef_2 <> 0)) (PreH14 : (l12 = (cons (x) (l13)))) (PreH15 : (p1_coef <> 0)) (PreH16 : (p1 <> 0)) (PreH17 : (n = (num_pre + 1 ))) (PreH18 : (1 <= cur_num_pre)) (PreH19 : (cur_num_pre < n)) (PreH20 : (InequList_nth_pos cur_num_pre l1 )) (PreH21 : (InequList_nth_neg cur_num_pre l2 )) (PreH22 : (l1 = (app (l11) (l12)))) (PreH23 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH24 : (l3 = (app (l4) (l_init)))) (PreH25 : (LP_abs_in_int_range n l3 )) (PreH26 : (n = (num_pre + 1 ))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < n)) (PreH29 : (n <= INT_MAX)) (PreH30 : (InequList_nth_pos cur_num_pre l1 )) (PreH31 : (InequList_nth_neg cur_num_pre l2 )) (PreH32 : (LP_abs_in_int_range n l1 )) (PreH33 : (LP_abs_in_int_range n l2 )) (PreH34 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ (p2 <> 0) ”
.

Definition generate_new_constraint_list_partial_solve_wit_2_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (PreH1 : (p2 <> 0)) (PreH2 : (n = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n)) (PreH5 : (InequList_nth_pos cur_num_pre l1 )) (PreH6 : (InequList_nth_neg cur_num_pre l2 )) (PreH7 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH8 : (l2 = (app (l21) (l22)))) (PreH9 : (p1_2 <> 0)) (PreH10 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH11 : (l3_2 = (app (l4_2) (l_init)))) (PreH12 : (LP_abs_in_int_range n l3_2 )) (PreH13 : (p1_coef_2 <> 0)) (PreH14 : (l12 = (cons (x) (l13)))) (PreH15 : (p1_coef <> 0)) (PreH16 : (p1 <> 0)) (PreH17 : (n = (num_pre + 1 ))) (PreH18 : (1 <= cur_num_pre)) (PreH19 : (cur_num_pre < n)) (PreH20 : (InequList_nth_pos cur_num_pre l1 )) (PreH21 : (InequList_nth_neg cur_num_pre l2 )) (PreH22 : (l1 = (app (l11) (l12)))) (PreH23 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH24 : (l3 = (app (l4) (l_init)))) (PreH25 : (LP_abs_in_int_range n l3 )) (PreH26 : (n = (num_pre + 1 ))) (PreH27 : (1 <= cur_num_pre)) (PreH28 : (cur_num_pre < n)) (PreH29 : (n <= INT_MAX)) (PreH30 : (InequList_nth_pos cur_num_pre l1 )) (PreH31 : (InequList_nth_neg cur_num_pre l2 )) (PreH32 : (LP_abs_in_int_range n l1 )) (PreH33 : (LP_abs_in_int_range n l2 )) (PreH34 : (LP_abs_in_int_range n l_init )) ,
  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  (InequList res n l3_2 )
|--
  “ (p2 <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11_2) ((cons (x1) (l12_2))))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (p1_2 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 ) ” 
  &&  “ (l3_2 = (app (l4_2) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3_2 ) ” 
  &&  “ (p1_coef_2 <> 0) ” 
  &&  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef_2 n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
.

Definition generate_new_constraint_list_partial_solve_wit_2 := generate_new_constraint_list_partial_solve_wit_2_pure -> generate_new_constraint_list_partial_solve_wit_2_aux.

Definition generate_new_constraint_list_partial_solve_wit_3_pure := 
(
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef_2: Z) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) (PreH1 : (l22 = (cons (x) (l23)))) (PreH2 : (p2_coef <> 0)) (PreH3 : (p2 <> 0)) (PreH4 : (n = (num_pre + 1 ))) (PreH5 : (1 <= cur_num_pre)) (PreH6 : (cur_num_pre < n)) (PreH7 : (InequList_nth_pos cur_num_pre l1 )) (PreH8 : (InequList_nth_neg cur_num_pre l2 )) (PreH9 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH10 : (l2 = (app (l21) (l22)))) (PreH11 : (p1_2 <> 0)) (PreH12 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH13 : (l3_2 = (app (l4_2) (l_init)))) (PreH14 : (LP_abs_in_int_range n l3_2 )) (PreH15 : (p1_coef <> 0)) (PreH16 : (l12 = (cons (x_2) (l13)))) (PreH17 : (p1_coef_2 <> 0)) (PreH18 : (p1 <> 0)) (PreH19 : (n = (num_pre + 1 ))) (PreH20 : (1 <= cur_num_pre)) (PreH21 : (cur_num_pre < n)) (PreH22 : (InequList_nth_pos cur_num_pre l1 )) (PreH23 : (InequList_nth_neg cur_num_pre l2 )) (PreH24 : (l1 = (app (l11) (l12)))) (PreH25 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH26 : (l3 = (app (l4) (l_init)))) (PreH27 : (LP_abs_in_int_range n l3 )) (PreH28 : (n = (num_pre + 1 ))) (PreH29 : (1 <= cur_num_pre)) (PreH30 : (cur_num_pre < n)) (PreH31 : (n <= INT_MAX)) (PreH32 : (InequList_nth_pos cur_num_pre l1 )) (PreH33 : (InequList_nth_neg cur_num_pre l2 )) (PreH34 : (LP_abs_in_int_range n l1 )) (PreH35 : (LP_abs_in_int_range n l2 )) (PreH36 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (x) (0))) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x) (0)) < 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x1) (0)) > 0) ”
) \/
(
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef_2: Z) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (l22 = (cons (x) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef <> 0)) (PreH20 : (l12 = (cons (x_2) (l13)))) (PreH21 : (p1_coef_2 <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ ((coef_Znth (cur_num_pre) (x1) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x) (0)) < 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (x) (0))) <= INT_MAX) ”
).

Definition generate_new_constraint_list_partial_solve_wit_3_pure_split_goal_1 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef_2: Z) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (l22 = (cons (x) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef <> 0)) (PreH20 : (l12 = (cons (x_2) (l13)))) (PreH21 : (p1_coef_2 <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ ((coef_Znth (cur_num_pre) (x1) (0)) > 0) ”
.

Definition generate_new_constraint_list_partial_solve_wit_3_pure_split_goal_2 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef_2: Z) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (l22 = (cons (x) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef <> 0)) (PreH20 : (l12 = (cons (x_2) (l13)))) (PreH21 : (p1_coef_2 <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ ((coef_Znth (cur_num_pre) (x1) (0)) <= INT_MAX) ”
.

Definition generate_new_constraint_list_partial_solve_wit_3_pure_split_goal_3 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef_2: Z) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (l22 = (cons (x) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef <> 0)) (PreH20 : (l12 = (cons (x_2) (l13)))) (PreH21 : (p1_coef_2 <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ ((coef_Znth (cur_num_pre) (x) (0)) < 0) ”
.

Definition generate_new_constraint_list_partial_solve_wit_3_pure_split_goal_4 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef_2: Z) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (l22 = (cons (x) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef <> 0)) (PreH20 : (l12 = (cons (x_2) (l13)))) (PreH21 : (p1_coef_2 <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ ((-(coef_Znth (cur_num_pre) (x) (0))) <= INT_MAX) ”
.

Definition generate_new_constraint_list_partial_solve_wit_3_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef_2: Z) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) (PreH1 : (l22 = (cons (x) (l23)))) (PreH2 : (p2_coef <> 0)) (PreH3 : (p2 <> 0)) (PreH4 : (n = (num_pre + 1 ))) (PreH5 : (1 <= cur_num_pre)) (PreH6 : (cur_num_pre < n)) (PreH7 : (InequList_nth_pos cur_num_pre l1 )) (PreH8 : (InequList_nth_neg cur_num_pre l2 )) (PreH9 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH10 : (l2 = (app (l21) (l22)))) (PreH11 : (p1_2 <> 0)) (PreH12 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH13 : (l3_2 = (app (l4_2) (l_init)))) (PreH14 : (LP_abs_in_int_range n l3_2 )) (PreH15 : (p1_coef <> 0)) (PreH16 : (l12 = (cons (x_2) (l13)))) (PreH17 : (p1_coef_2 <> 0)) (PreH18 : (p1 <> 0)) (PreH19 : (n = (num_pre + 1 ))) (PreH20 : (1 <= cur_num_pre)) (PreH21 : (cur_num_pre < n)) (PreH22 : (InequList_nth_pos cur_num_pre l1 )) (PreH23 : (InequList_nth_neg cur_num_pre l2 )) (PreH24 : (l1 = (app (l11) (l12)))) (PreH25 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH26 : (l3 = (app (l4) (l_init)))) (PreH27 : (LP_abs_in_int_range n l3 )) (PreH28 : (n = (num_pre + 1 ))) (PreH29 : (1 <= cur_num_pre)) (PreH30 : (cur_num_pre < n)) (PreH31 : (n <= INT_MAX)) (PreH32 : (InequList_nth_pos cur_num_pre l1 )) (PreH33 : (InequList_nth_neg cur_num_pre l2 )) (PreH34 : (LP_abs_in_int_range n l1 )) (PreH35 : (LP_abs_in_int_range n l2 )) (PreH36 : (LP_abs_in_int_range n l_init )) ,
  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
|--
  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (x) (0))) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x) (0)) < 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x1) (0)) <= INT_MAX) ” 
  &&  “ ((coef_Znth (cur_num_pre) (x1) (0)) > 0) ” 
  &&  “ (l22 = (cons (x) (l23))) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11_2) ((cons (x1) (l12_2))))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (p1_2 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 ) ” 
  &&  “ (l3_2 = (app (l4_2) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3_2 ) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (l12 = (cons (x_2) (l13))) ” 
  &&  “ (p1_coef_2 <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
.

Definition generate_new_constraint_list_partial_solve_wit_3 := generate_new_constraint_list_partial_solve_wit_3_pure -> generate_new_constraint_list_partial_solve_wit_3_aux.

Definition generate_new_constraint_list_partial_solve_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (l22 = (cons (x_2) (l23)))) (PreH4 : (p2_coef <> 0)) (PreH5 : (p2 <> 0)) (PreH6 : (n = (num_pre + 1 ))) (PreH7 : (1 <= cur_num_pre)) (PreH8 : (cur_num_pre < n)) (PreH9 : (InequList_nth_pos cur_num_pre l1 )) (PreH10 : (InequList_nth_neg cur_num_pre l2 )) (PreH11 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH12 : (l2 = (app (l21) (l22)))) (PreH13 : (p1_2 <> 0)) (PreH14 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH15 : (l3_2 = (app (l4_2) (l_init)))) (PreH16 : (LP_abs_in_int_range n l3_2 )) (PreH17 : (p1_coef_2 <> 0)) (PreH18 : (l12 = (cons (x) (l13)))) (PreH19 : (p1_coef <> 0)) (PreH20 : (p1 <> 0)) (PreH21 : (n = (num_pre + 1 ))) (PreH22 : (1 <= cur_num_pre)) (PreH23 : (cur_num_pre < n)) (PreH24 : (InequList_nth_pos cur_num_pre l1 )) (PreH25 : (InequList_nth_neg cur_num_pre l2 )) (PreH26 : (l1 = (app (l11) (l12)))) (PreH27 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH28 : (l3 = (app (l4) (l_init)))) (PreH29 : (LP_abs_in_int_range n l3 )) (PreH30 : (n = (num_pre + 1 ))) (PreH31 : (1 <= cur_num_pre)) (PreH32 : (cur_num_pre < n)) (PreH33 : (n <= INT_MAX)) (PreH34 : (InequList_nth_pos cur_num_pre l1 )) (PreH35 : (InequList_nth_neg cur_num_pre l2 )) (PreH36 : (LP_abs_in_int_range n l1 )) (PreH37 : (LP_abs_in_int_range n l2 )) (PreH38 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
|--
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (l22 = (cons (x_2) (l23))) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11_2) ((cons (x1) (l12_2))))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (p1_2 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 ) ” 
  &&  “ (l3_2 = (app (l4_2) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3_2 ) ” 
  &&  “ (p1_coef_2 <> 0) ” 
  &&  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (InequList res n l3_2 )
  **  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
.

Definition generate_new_constraint_list_partial_solve_wit_5_pure := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (generate_new_constraint cur_num_pre x1 x_2 c3 )) (PreH4 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH5 : (l22 = (cons (x_2) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef_2 <> 0)) (PreH20 : (l12 = (cons (x) (l13)))) (PreH21 : (p1_coef <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (coef_array retval (num_pre + 1 ) c3 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  “ (retval <> 0) ”
.

Definition generate_new_constraint_list_partial_solve_wit_5_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (p1_coef: Z) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (generate_new_constraint cur_num_pre x1 x_2 c3 )) (PreH4 : (abs_in_int_range (num_pre + 1 ) c3 )) (PreH5 : (l22 = (cons (x_2) (l23)))) (PreH6 : (p2_coef <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (n = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n)) (PreH11 : (InequList_nth_pos cur_num_pre l1 )) (PreH12 : (InequList_nth_neg cur_num_pre l2 )) (PreH13 : (l1 = (app (l11_2) ((cons (x1) (l12_2)))))) (PreH14 : (l2 = (app (l21) (l22)))) (PreH15 : (p1_2 <> 0)) (PreH16 : (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 )) (PreH17 : (l3_2 = (app (l4_2) (l_init)))) (PreH18 : (LP_abs_in_int_range n l3_2 )) (PreH19 : (p1_coef_2 <> 0)) (PreH20 : (l12 = (cons (x) (l13)))) (PreH21 : (p1_coef <> 0)) (PreH22 : (p1 <> 0)) (PreH23 : (n = (num_pre + 1 ))) (PreH24 : (1 <= cur_num_pre)) (PreH25 : (cur_num_pre < n)) (PreH26 : (InequList_nth_pos cur_num_pre l1 )) (PreH27 : (InequList_nth_neg cur_num_pre l2 )) (PreH28 : (l1 = (app (l11) (l12)))) (PreH29 : (generate_new_constraints cur_num_pre l11 l2 l4 )) (PreH30 : (l3 = (app (l4) (l_init)))) (PreH31 : (LP_abs_in_int_range n l3 )) (PreH32 : (n = (num_pre + 1 ))) (PreH33 : (1 <= cur_num_pre)) (PreH34 : (cur_num_pre < n)) (PreH35 : (n <= INT_MAX)) (PreH36 : (InequList_nth_pos cur_num_pre l1 )) (PreH37 : (InequList_nth_neg cur_num_pre l2 )) (PreH38 : (LP_abs_in_int_range n l1 )) (PreH39 : (LP_abs_in_int_range n l2 )) (PreH40 : (LP_abs_in_int_range n l_init )) ,
  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (coef_array retval (num_pre + 1 ) c3 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (generate_new_constraint cur_num_pre x1 x_2 c3 ) ” 
  &&  “ (abs_in_int_range (num_pre + 1 ) c3 ) ” 
  &&  “ (l22 = (cons (x_2) (l23))) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11_2) ((cons (x1) (l12_2))))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (p1_2 <> 0) ” 
  &&  “ (generate_new_constraints_partial cur_num_pre l11_2 x1 l21 l22 l4_2 ) ” 
  &&  “ (l3_2 = (app (l4_2) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3_2 ) ” 
  &&  “ (p1_coef_2 <> 0) ” 
  &&  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (l1 = (app (l11) (l12))) ” 
  &&  “ (generate_new_constraints cur_num_pre l11 l2 l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init))) ” 
  &&  “ (LP_abs_in_int_range n l3 ) ” 
  &&  “ (n = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1 ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2 ) ” 
  &&  “ (LP_abs_in_int_range n l1 ) ” 
  &&  “ (LP_abs_in_int_range n l2 ) ” 
  &&  “ (LP_abs_in_int_range n l_init ) ”
  &&  (coef_array retval (num_pre + 1 ) c3 )
  **  (InequList res (num_pre + 1 ) l3_2 )
  **  (coef_array p1_coef_2 (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
.

Definition generate_new_constraint_list_partial_solve_wit_5 := generate_new_constraint_list_partial_solve_wit_5_pure -> generate_new_constraint_list_partial_solve_wit_5_aux.

Definition generate_new_constraint_list_which_implies_wit_1 := 
forall (n: Z) (l12: (@list Constraint)) (l11: (@list Constraint)) (p1: Z) (r1: Z) (PreH1 : (p1 <> 0)) ,
  (InequList_seg r1 p1 n l11 )
  **  (InequList p1 n l12 )
|--
  EX (p1_next: Z)  (p1_coef: Z)  (x: Constraint)  (l13: (@list Constraint)) ,
  “ (l12 = (cons (x) (l13))) ” 
  &&  “ (p1_coef <> 0) ”
  &&  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (InequList_seg r1 p1 n l11 )
  **  (coef_array p1_coef n x )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l13 )
.

Definition generate_new_constraint_list_which_implies_wit_2 := 
forall (n: Z) (l22: (@list Constraint)) (l21: (@list Constraint)) (p2: Z) (r2: Z) (PreH1 : (p2 <> 0)) ,
  (InequList_seg r2 p2 n l21 )
  **  (InequList p2 n l22 )
|--
  EX (p2_next: Z)  (p2_coef: Z)  (x: Constraint)  (l23: (@list Constraint)) ,
  “ (l22 = (cons (x) (l23))) ” 
  &&  “ (p2_coef <> 0) ”
  &&  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2 p2 n l21 )
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
.

(*----- Function real_shadow -----*)

Definition real_shadow_safety_wit_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (0 <= cnt)) (PreH4 : (cnt <= n_pre)) (PreH5 : (LP_implies l1 l2 )) (PreH6 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0_upper = 0)) (PreH14 : (BP0_lower = 0)) (PreH15 : (BP0_remain = 0)) (PreH16 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition real_shadow_safety_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (eliminate_xn cnt l2 b )) (PreH2 : (form_BP up lo re b )) (PreH3 : (InequList_nth_pos cnt up )) (PreH4 : (InequList_nth_neg cnt lo )) (PreH5 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH6 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH8 : (cnt >= 1)) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (LP_implies l1 l2 )) (PreH14 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) (PreH18 : (n_pre >= 1)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (n_pre <= (INT_MAX - 1 ))) (PreH21 : (BP0_upper = 0)) (PreH22 : (BP0_lower = 0)) (PreH23 : (BP0_remain = 0)) (PreH24 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain_2 = 0)) (PreH2 : (eliminate_xn cnt l2 b )) (PreH3 : (form_BP up lo re b )) (PreH4 : (InequList_nth_pos cnt up )) (PreH5 : (InequList_nth_neg cnt lo )) (PreH6 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH9 : (cnt >= 1)) (PreH10 : (BP0 <> 0)) (PreH11 : (pr_pre <> 0)) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= n_pre)) (PreH14 : (LP_implies l1 l2 )) (PreH15 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH16 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (n_pre >= 1)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : (n_pre <= (INT_MAX - 1 ))) (PreH22 : (BP0_upper = 0)) (PreH23 : (BP0_lower = 0)) (PreH24 : (BP0_remain = 0)) (PreH25 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2 )) (PreH16 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_5 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2 )) (PreH16 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> 0)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 <> 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2 )) (PreH16 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain_2 <> 0)) (PreH2 : (eliminate_xn cnt l2 b )) (PreH3 : (form_BP up lo re b )) (PreH4 : (InequList_nth_pos cnt up )) (PreH5 : (InequList_nth_neg cnt lo )) (PreH6 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH9 : (cnt >= 1)) (PreH10 : (BP0 <> 0)) (PreH11 : (pr_pre <> 0)) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= n_pre)) (PreH14 : (LP_implies l1 l2 )) (PreH15 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH16 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (n_pre >= 1)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : (n_pre <= (INT_MAX - 1 ))) (PreH22 : (BP0_upper = 0)) (PreH23 : (BP0_lower = 0)) (PreH24 : (BP0_remain = 0)) (PreH25 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain_2 <> 0)) (PreH2 : (BP0_upper_2 <> 0)) (PreH3 : (BP0_remain_2 = 0)) (PreH4 : (eliminate_xn cnt l2 b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (InequList_nth_pos cnt up )) (PreH7 : (InequList_nth_neg cnt lo )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH11 : (cnt >= 1)) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= n_pre)) (PreH16 : (LP_implies l1 l2 )) (PreH17 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH18 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH19 : (BP0 <> 0)) (PreH20 : (pr_pre <> 0)) (PreH21 : (n_pre >= 1)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre <= (INT_MAX - 1 ))) (PreH24 : (BP0_upper = 0)) (PreH25 : (BP0_lower = 0)) (PreH26 : (BP0_remain = 0)) (PreH27 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ False ”
.

Definition real_shadow_safety_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain_2 = 0)) (PreH2 : (BP0_remain_2 <> 0)) (PreH3 : (eliminate_xn cnt l2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2 )) (PreH16 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ False ”
.

Definition real_shadow_safety_wit_10 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain_2 = 0)) (PreH2 : (BP0_upper_2 <> 0)) (PreH3 : (BP0_remain_2 = 0)) (PreH4 : (eliminate_xn cnt l2 b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (InequList_nth_pos cnt up )) (PreH7 : (InequList_nth_neg cnt lo )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH11 : (cnt >= 1)) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= n_pre)) (PreH16 : (LP_implies l1 l2 )) (PreH17 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH18 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH19 : (BP0 <> 0)) (PreH20 : (pr_pre <> 0)) (PreH21 : (n_pre >= 1)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre <= (INT_MAX - 1 ))) (PreH24 : (BP0_upper = 0)) (PreH25 : (BP0_lower = 0)) (PreH26 : (BP0_remain = 0)) (PreH27 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_11 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2 )) (PreH18 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_12 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2 )) (PreH18 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> 0)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_13 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (BP0_remain_2 <> 0)) (PreH3 : (BP0_remain_2 <> 0)) (PreH4 : (eliminate_xn cnt l2 b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (InequList_nth_pos cnt up )) (PreH7 : (InequList_nth_neg cnt lo )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH11 : (cnt >= 1)) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= n_pre)) (PreH16 : (LP_implies l1 l2 )) (PreH17 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH18 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH19 : (BP0 <> 0)) (PreH20 : (pr_pre <> 0)) (PreH21 : (n_pre >= 1)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre <= (INT_MAX - 1 ))) (PreH24 : (BP0_upper = 0)) (PreH25 : (BP0_lower = 0)) (PreH26 : (BP0_remain = 0)) (PreH27 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_14 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH4 : (BP0_remain_2 <> 0)) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (eliminate_xn cnt l2 b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (InequList_nth_pos cnt up )) (PreH9 : (InequList_nth_neg cnt lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH13 : (cnt >= 1)) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= n_pre)) (PreH18 : (LP_implies l1 l2 )) (PreH19 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH21 : (BP0 <> 0)) (PreH22 : (pr_pre <> 0)) (PreH23 : (n_pre >= 1)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre <= (INT_MAX - 1 ))) (PreH26 : (BP0_upper = 0)) (PreH27 : (BP0_lower = 0)) (PreH28 : (BP0_remain = 0)) (PreH29 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_15 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (BP0_lower_2 <> 0)) (PreH3 : (BP0_remain_2 = 0)) (PreH4 : (BP0_upper_2 <> 0)) (PreH5 : (BP0_remain_2 = 0)) (PreH6 : (eliminate_xn cnt l2 b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (InequList_nth_pos cnt up )) (PreH9 : (InequList_nth_neg cnt lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH13 : (cnt >= 1)) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= n_pre)) (PreH18 : (LP_implies l1 l2 )) (PreH19 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH21 : (BP0 <> 0)) (PreH22 : (pr_pre <> 0)) (PreH23 : (n_pre >= 1)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre <= (INT_MAX - 1 ))) (PreH26 : (BP0_upper = 0)) (PreH27 : (BP0_lower = 0)) (PreH28 : (BP0_remain = 0)) (PreH29 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_16 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH4 : (BP0_lower_2 <> 0)) (PreH5 : (BP0_remain_2 = 0)) (PreH6 : (BP0_upper_2 <> 0)) (PreH7 : (BP0_remain_2 = 0)) (PreH8 : (eliminate_xn cnt l2 b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (InequList_nth_pos cnt up )) (PreH11 : (InequList_nth_neg cnt lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH15 : (cnt >= 1)) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) (PreH18 : (0 <= cnt)) (PreH19 : (cnt <= n_pre)) (PreH20 : (LP_implies l1 l2 )) (PreH21 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH22 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH23 : (BP0 <> 0)) (PreH24 : (pr_pre <> 0)) (PreH25 : (n_pre >= 1)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (n_pre <= (INT_MAX - 1 ))) (PreH28 : (BP0_upper = 0)) (PreH29 : (BP0_lower = 0)) (PreH30 : (BP0_remain = 0)) (PreH31 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_17 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (BP0_remain_2 <> 0)) (PreH4 : (BP0_remain_2 <> 0)) (PreH5 : (eliminate_xn cnt l2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2 )) (PreH18 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ False ”
.

Definition real_shadow_safety_wit_18 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (BP0_lower_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (BP0_upper_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (eliminate_xn cnt l2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2 )) (PreH20 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ False ”
.

Definition real_shadow_safety_wit_19 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (BP0_remain_2 <> 0)) (PreH4 : (BP0_remain_2 <> 0)) (PreH5 : (eliminate_xn cnt l2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2 )) (PreH18 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition real_shadow_safety_wit_20 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2 )) (PreH20 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition real_shadow_safety_wit_21 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (BP0_lower_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (BP0_upper_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (eliminate_xn cnt l2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2 )) (PreH20 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition real_shadow_safety_wit_22 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2 )) (PreH22 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition real_shadow_safety_wit_23 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2 )) (PreH20 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ ((cnt - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt - 1 )) ”
.

Definition real_shadow_safety_wit_24 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2 )) (PreH22 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ ((cnt - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt - 1 )) ”
.

Definition real_shadow_safety_wit_25 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (PreH1 : (cnt < 1)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (0 <= cnt)) (PreH5 : (cnt <= n_pre)) (PreH6 : (LP_implies l1 l2 )) (PreH7 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0_upper = 0)) (PreH15 : (BP0_lower = 0)) (PreH16 : (BP0_remain = 0)) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> r)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_entail_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList p1 (n_pre + 1 ) l1 )
|--
  EX (l2: (@list Constraint)) ,
  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (n_pre + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList p1 (n_pre + 1 ) l2 )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  TT && emp 
|--
  “ (InequList_Zeros l1 (n_pre + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_implies l1 l1 ) ”
  &&  emp
).

Definition real_shadow_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList_Zeros l1 (n_pre + 1 ) (n_pre + 1 ) )
.

Definition real_shadow_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (LP_implies l1 l1 )
.

Definition real_shadow_entail_wit_2_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  EX (l2: (@list Constraint)) ,
  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= (cnt - 1 )) ” 
  &&  “ ((cnt - 1 ) <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 ((cnt - 1 ) + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList retval (n_pre + 1 ) l2 )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  TT && emp 
|--
  “ (InequList_Zeros l3 ((cnt - 1 ) + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_implies l1 l3 ) ”
  &&  emp
).

Definition real_shadow_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList_Zeros l3 ((cnt - 1 ) + 1 ) (n_pre + 1 ) )
.

Definition real_shadow_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (LP_implies l1 l3 )
.

Definition real_shadow_entail_wit_2_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2_2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2_2 )) (PreH22 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  EX (l2: (@list Constraint)) ,
  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= (cnt - 1 )) ” 
  &&  “ ((cnt - 1 ) <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 ((cnt - 1 ) + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList retval (n_pre + 1 ) l2 )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2_2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2_2 )) (PreH22 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  TT && emp 
|--
  “ (InequList_Zeros l3 ((cnt - 1 ) + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_implies l1 l3 ) ”
  &&  emp
).

Definition real_shadow_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2_2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2_2 )) (PreH22 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList_Zeros l3 ((cnt - 1 ) + 1 ) (n_pre + 1 ) )
.

Definition real_shadow_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2_2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2_2 )) (PreH22 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (LP_implies l1 l3 )
.

Definition real_shadow_return_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2_2: (@list Constraint)) (cnt: Z) (PreH1 : (cnt < 1)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (0 <= cnt)) (PreH5 : (cnt <= n_pre)) (PreH6 : (LP_implies l1 l2_2 )) (PreH7 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0_upper = 0)) (PreH15 : (BP0_lower = 0)) (PreH16 : (BP0_remain = 0)) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2_2 )
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (0 = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (PreH1 : (cnt < 1)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (0 <= cnt)) (PreH5 : (cnt <= n_pre)) (PreH6 : (LP_implies l1 l2_2 )) (PreH7 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0_upper = 0)) (PreH15 : (BP0_lower = 0)) (PreH16 : (BP0_remain = 0)) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  TT && emp 
|--
  “ (InequList_Zeros l2_2 1 (n_pre + 1 ) ) ”
  &&  emp
).

Definition real_shadow_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (PreH1 : (cnt < 1)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (0 <= cnt)) (PreH5 : (cnt <= n_pre)) (PreH6 : (LP_implies l1 l2_2 )) (PreH7 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0_upper = 0)) (PreH15 : (BP0_lower = 0)) (PreH16 : (BP0_remain = 0)) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList_Zeros l2_2 1 (n_pre + 1 ) )
.

Definition real_shadow_return_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (BP0_remain_2 <> 0)) (PreH4 : (BP0_remain_2 <> 0)) (PreH5 : (eliminate_xn cnt l2_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2_2 )) (PreH18 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (1 = 1) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition real_shadow_return_wit_3 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (1 = 1) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
|--
  TT && emp 
).

Definition real_shadow_return_wit_3_split_goal_spatial := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (BP0_remain_2 <> 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
|--
  TT && emp 
.

Definition real_shadow_return_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (BP0_lower_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (BP0_upper_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (eliminate_xn cnt l2_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (InequList_nth_pos cnt up )) (PreH10 : (InequList_nth_neg cnt lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH14 : (cnt >= 1)) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= n_pre)) (PreH19 : (LP_implies l1 l2_2 )) (PreH20 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH22 : (BP0 <> 0)) (PreH23 : (pr_pre <> 0)) (PreH24 : (n_pre >= 1)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre <= (INT_MAX - 1 ))) (PreH27 : (BP0_upper = 0)) (PreH28 : (BP0_lower = 0)) (PreH29 : (BP0_remain = 0)) (PreH30 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (1 = 1) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition real_shadow_return_wit_5 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2_2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2_2 )) (PreH22 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (1 = 1) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2_2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2_2 )) (PreH22 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
|--
  TT && emp 
).

Definition real_shadow_return_wit_5_split_goal_spatial := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH5 : (BP0_lower_2 <> 0)) (PreH6 : (BP0_remain_2 = 0)) (PreH7 : (BP0_upper_2 <> 0)) (PreH8 : (BP0_remain_2 = 0)) (PreH9 : (eliminate_xn cnt l2_2 b )) (PreH10 : (form_BP up lo re b )) (PreH11 : (InequList_nth_pos cnt up )) (PreH12 : (InequList_nth_neg cnt lo )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH15 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH16 : (cnt >= 1)) (PreH17 : (BP0 <> 0)) (PreH18 : (pr_pre <> 0)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= n_pre)) (PreH21 : (LP_implies l1 l2_2 )) (PreH22 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH23 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH24 : (BP0 <> 0)) (PreH25 : (pr_pre <> 0)) (PreH26 : (n_pre >= 1)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre <= (INT_MAX - 1 ))) (PreH29 : (BP0_upper = 0)) (PreH30 : (BP0_lower = 0)) (PreH31 : (BP0_remain = 0)) (PreH32 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList retval (n_pre + 1 ) l3 )
|--
  TT && emp 
.

Definition real_shadow_return_wit_6 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2_2 )) (PreH18 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> 0)
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (0 = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2_2 )) (PreH18 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  “ (InequList_Zeros (@nil Constraint) 1 (n_pre + 1 ) ) ” 
  &&  “ (LP_implies l1 (@nil Constraint) ) ”
  &&  emp
).

Definition real_shadow_return_wit_6_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2_2 )) (PreH18 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  “ (InequList_Zeros (@nil Constraint) 1 (n_pre + 1 ) ) ”
.

Definition real_shadow_return_wit_6_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2_2 )) (PreH18 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  “ (LP_implies l1 (@nil Constraint) ) ”
.

Definition real_shadow_return_wit_6_split_goal_spatial := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2_2 )) (PreH18 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  TT && emp 
.

Definition real_shadow_return_wit_7 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2_2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2_2 )) (PreH16 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> 0)
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (0 = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2_2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2_2 )) (PreH16 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  “ (InequList_Zeros (@nil Constraint) 1 (n_pre + 1 ) ) ” 
  &&  “ (LP_implies l1 (@nil Constraint) ) ”
  &&  emp
).

Definition real_shadow_return_wit_7_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2_2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2_2 )) (PreH16 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  “ (InequList_Zeros (@nil Constraint) 1 (n_pre + 1 ) ) ”
.

Definition real_shadow_return_wit_7_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2_2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2_2 )) (PreH16 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  “ (LP_implies l1 (@nil Constraint) ) ”
.

Definition real_shadow_return_wit_7_split_goal_spatial := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2_2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2_2 )) (PreH16 : (InequList_Zeros l2_2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2_2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
|--
  TT && emp 
.

Definition real_shadow_partial_solve_wit_1_pure := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (PreH1 : (cnt >= 1)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (0 <= cnt)) (PreH5 : (cnt <= n_pre)) (PreH6 : (LP_implies l1 l2 )) (PreH7 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0_upper = 0)) (PreH15 : (BP0_lower = 0)) (PreH16 : (BP0_remain = 0)) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ”
.

Definition real_shadow_partial_solve_wit_1_aux := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (PreH1 : (cnt >= 1)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (0 <= cnt)) (PreH5 : (cnt <= n_pre)) (PreH6 : (LP_implies l1 l2 )) (PreH7 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0_upper = 0)) (PreH15 : (BP0_lower = 0)) (PreH16 : (BP0_remain = 0)) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r (n_pre + 1 ) l2 )
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_1 := real_shadow_partial_solve_wit_1_pure -> real_shadow_partial_solve_wit_1_aux.

Definition real_shadow_partial_solve_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (eliminate_xn cnt l2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2 )) (PreH16 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (BP0_upper_2 = 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 = 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2 )) (PreH18 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (BP0_lower_2 = 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (BP0_upper_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_4_pure := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain_2 <> 0)) (PreH2 : (BP0_remain_2 <> 0)) (PreH3 : (eliminate_xn cnt l2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2 )) (PreH16 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ”
.

Definition real_shadow_partial_solve_wit_4_aux := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain_2 <> 0)) (PreH2 : (BP0_remain_2 <> 0)) (PreH3 : (eliminate_xn cnt l2 b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (InequList_nth_pos cnt up )) (PreH6 : (InequList_nth_neg cnt lo )) (PreH7 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH10 : (cnt >= 1)) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= n_pre)) (PreH15 : (LP_implies l1 l2 )) (PreH16 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH17 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH18 : (BP0 <> 0)) (PreH19 : (pr_pre <> 0)) (PreH20 : (n_pre >= 1)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (n_pre <= (INT_MAX - 1 ))) (PreH23 : (BP0_upper = 0)) (PreH24 : (BP0_lower = 0)) (PreH25 : (BP0_remain = 0)) (PreH26 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_4 := real_shadow_partial_solve_wit_4_pure -> real_shadow_partial_solve_wit_4_aux.

Definition real_shadow_partial_solve_wit_5_pure := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 <> 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2 )) (PreH18 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ”
.

Definition real_shadow_partial_solve_wit_5_aux := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower_2 <> 0)) (PreH2 : (BP0_remain_2 = 0)) (PreH3 : (BP0_upper_2 <> 0)) (PreH4 : (BP0_remain_2 = 0)) (PreH5 : (eliminate_xn cnt l2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (InequList_nth_pos cnt up )) (PreH8 : (InequList_nth_neg cnt lo )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH12 : (cnt >= 1)) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= n_pre)) (PreH17 : (LP_implies l1 l2 )) (PreH18 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH20 : (BP0 <> 0)) (PreH21 : (pr_pre <> 0)) (PreH22 : (n_pre >= 1)) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre <= (INT_MAX - 1 ))) (PreH25 : (BP0_upper = 0)) (PreH26 : (BP0_lower = 0)) (PreH27 : (BP0_remain = 0)) (PreH28 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (BP0_lower_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (BP0_upper_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_5 := real_shadow_partial_solve_wit_5_pure -> real_shadow_partial_solve_wit_5_aux.

Definition real_shadow_partial_solve_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (BP0_remain_2 <> 0)) (PreH3 : (BP0_remain_2 <> 0)) (PreH4 : (eliminate_xn cnt l2 b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (InequList_nth_pos cnt up )) (PreH7 : (InequList_nth_neg cnt lo )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH11 : (cnt >= 1)) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= n_pre)) (PreH16 : (LP_implies l1 l2 )) (PreH17 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH18 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH19 : (BP0 <> 0)) (PreH20 : (pr_pre <> 0)) (PreH21 : (n_pre >= 1)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre <= (INT_MAX - 1 ))) (PreH24 : (BP0_upper = 0)) (PreH25 : (BP0_lower = 0)) (PreH26 : (BP0_remain = 0)) (PreH27 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (retval = 0) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH4 : (BP0_remain_2 <> 0)) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (eliminate_xn cnt l2 b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (InequList_nth_pos cnt up )) (PreH9 : (InequList_nth_neg cnt lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH13 : (cnt >= 1)) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= n_pre)) (PreH18 : (LP_implies l1 l2 )) (PreH19 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH21 : (BP0 <> 0)) (PreH22 : (pr_pre <> 0)) (PreH23 : (n_pre >= 1)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre <= (INT_MAX - 1 ))) (PreH26 : (BP0_upper = 0)) (PreH27 : (BP0_lower = 0)) (PreH28 : (BP0_remain = 0)) (PreH29 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l3 ) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (BP0_lower_2 <> 0)) (PreH3 : (BP0_remain_2 = 0)) (PreH4 : (BP0_upper_2 <> 0)) (PreH5 : (BP0_remain_2 = 0)) (PreH6 : (eliminate_xn cnt l2 b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (InequList_nth_pos cnt up )) (PreH9 : (InequList_nth_neg cnt lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH13 : (cnt >= 1)) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= n_pre)) (PreH18 : (LP_implies l1 l2 )) (PreH19 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH21 : (BP0 <> 0)) (PreH22 : (pr_pre <> 0)) (PreH23 : (n_pre >= 1)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre <= (INT_MAX - 1 ))) (PreH26 : (BP0_upper = 0)) (PreH27 : (BP0_lower = 0)) (PreH28 : (BP0_remain = 0)) (PreH29 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (retval = 0) ” 
  &&  “ (BP0_lower_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (BP0_upper_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH4 : (BP0_lower_2 <> 0)) (PreH5 : (BP0_remain_2 = 0)) (PreH6 : (BP0_upper_2 <> 0)) (PreH7 : (BP0_remain_2 = 0)) (PreH8 : (eliminate_xn cnt l2 b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (InequList_nth_pos cnt up )) (PreH11 : (InequList_nth_neg cnt lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH15 : (cnt >= 1)) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) (PreH18 : (0 <= cnt)) (PreH19 : (cnt <= n_pre)) (PreH20 : (LP_implies l1 l2 )) (PreH21 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH22 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH23 : (BP0 <> 0)) (PreH24 : (pr_pre <> 0)) (PreH25 : (n_pre >= 1)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (n_pre <= (INT_MAX - 1 ))) (PreH28 : (BP0_upper = 0)) (PreH29 : (BP0_lower = 0)) (PreH30 : (BP0_remain = 0)) (PreH31 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l3 ) ” 
  &&  “ (BP0_lower_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (BP0_upper_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_10 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (BP0_remain_2 <> 0)) (PreH3 : (BP0_remain_2 <> 0)) (PreH4 : (eliminate_xn cnt l2 b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (InequList_nth_pos cnt up )) (PreH7 : (InequList_nth_neg cnt lo )) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH11 : (cnt >= 1)) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= n_pre)) (PreH16 : (LP_implies l1 l2 )) (PreH17 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH18 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH19 : (BP0 <> 0)) (PreH20 : (pr_pre <> 0)) (PreH21 : (n_pre >= 1)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre <= (INT_MAX - 1 ))) (PreH24 : (BP0_upper = 0)) (PreH25 : (BP0_lower = 0)) (PreH26 : (BP0_remain = 0)) (PreH27 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (retval = 0) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_11 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH4 : (BP0_remain_2 <> 0)) (PreH5 : (BP0_remain_2 <> 0)) (PreH6 : (eliminate_xn cnt l2 b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (InequList_nth_pos cnt up )) (PreH9 : (InequList_nth_neg cnt lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH13 : (cnt >= 1)) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= n_pre)) (PreH18 : (LP_implies l1 l2 )) (PreH19 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH21 : (BP0 <> 0)) (PreH22 : (pr_pre <> 0)) (PreH23 : (n_pre >= 1)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre <= (INT_MAX - 1 ))) (PreH26 : (BP0_upper = 0)) (PreH27 : (BP0_lower = 0)) (PreH28 : (BP0_remain = 0)) (PreH29 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l3 ) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (BP0_remain_2 <> 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_12 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (BP0_lower_2 <> 0)) (PreH3 : (BP0_remain_2 = 0)) (PreH4 : (BP0_upper_2 <> 0)) (PreH5 : (BP0_remain_2 = 0)) (PreH6 : (eliminate_xn cnt l2 b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (InequList_nth_pos cnt up )) (PreH9 : (InequList_nth_neg cnt lo )) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH13 : (cnt >= 1)) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= n_pre)) (PreH18 : (LP_implies l1 l2 )) (PreH19 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH21 : (BP0 <> 0)) (PreH22 : (pr_pre <> 0)) (PreH23 : (n_pre >= 1)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre <= (INT_MAX - 1 ))) (PreH26 : (BP0_upper = 0)) (PreH27 : (BP0_lower = 0)) (PreH28 : (BP0_remain = 0)) (PreH29 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (retval = 0) ” 
  &&  “ (BP0_lower_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (BP0_upper_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_13 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (LP_abs_in_int_range (n_pre + 1 ) l3 )) (PreH4 : (BP0_lower_2 <> 0)) (PreH5 : (BP0_remain_2 = 0)) (PreH6 : (BP0_upper_2 <> 0)) (PreH7 : (BP0_remain_2 = 0)) (PreH8 : (eliminate_xn cnt l2 b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (InequList_nth_pos cnt up )) (PreH11 : (InequList_nth_neg cnt lo )) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) up )) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) lo )) (PreH14 : (LP_abs_in_int_range (n_pre + 1 ) re )) (PreH15 : (cnt >= 1)) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) (PreH18 : (0 <= cnt)) (PreH19 : (cnt <= n_pre)) (PreH20 : (LP_implies l1 l2 )) (PreH21 : (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) )) (PreH22 : (LP_abs_in_int_range (n_pre + 1 ) l2 )) (PreH23 : (BP0 <> 0)) (PreH24 : (pr_pre <> 0)) (PreH25 : (n_pre >= 1)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (n_pre <= (INT_MAX - 1 ))) (PreH28 : (BP0_upper = 0)) (PreH29 : (BP0_lower = 0)) (PreH30 : (BP0_remain = 0)) (PreH31 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l3 ) ” 
  &&  “ (BP0_lower_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (BP0_upper_2 <> 0) ” 
  &&  “ (BP0_remain_2 = 0) ” 
  &&  “ (eliminate_xn cnt l2 b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) up ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) lo ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) re ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 (cnt + 1 ) (n_pre + 1 ) ) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l2 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

(*----- Function lia_deduction -----*)

Definition lia_deduction_safety_wit_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) (PreH9 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lia_deduction_safety_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (p2: Z) (l2: (@list Constraint)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (LP_implies l1 l2 )) (PreH3 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH4 : (BP0 <> 0)) (PreH5 : (pr_pre <> 0)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= (INT_MAX - 1 ))) (PreH8 : (BP0_upper = 0)) (PreH9 : (BP0_lower = 0)) (PreH10 : (BP0_remain = 0)) (PreH11 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lia_deduction_safety_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = 1)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ False ”
.

Definition lia_deduction_safety_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (p2: Z) (l2: (@list Constraint)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = 0)) (PreH3 : (LP_implies l1 l2 )) (PreH4 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH5 : (BP0 <> 0)) (PreH6 : (pr_pre <> 0)) (PreH7 : (n_pre >= 1)) (PreH8 : (n_pre <= (INT_MAX - 1 ))) (PreH9 : (BP0_upper = 0)) (PreH10 : (BP0_lower = 0)) (PreH11 : (BP0_remain = 0)) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ False ”
.

Definition lia_deduction_safety_wit_5 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = 1)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition lia_deduction_safety_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = 1)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lia_deduction_safety_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (p2: Z) (l2: (@list Constraint)) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = 0)) (PreH3 : (LP_implies l1 l2 )) (PreH4 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH5 : (BP0 <> 0)) (PreH6 : (pr_pre <> 0)) (PreH7 : (n_pre >= 1)) (PreH8 : (n_pre <= (INT_MAX - 1 ))) (PreH9 : (BP0_upper = 0)) (PreH10 : (BP0_lower = 0)) (PreH11 : (BP0_remain = 0)) (PreH12 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "p" ) )) # Ptr  |-> p2)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (p2: Z) (l2: (@list Constraint)) (retval: Z) (PreH1 : (p2 = 0)) (PreH2 : (retval <> 1)) (PreH3 : (retval = 0)) (PreH4 : (LP_implies l1 l2 )) (PreH5 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH6 : (BP0 <> 0)) (PreH7 : (pr_pre <> 0)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0_upper = 0)) (PreH11 : (BP0_lower = 0)) (PreH12 : (BP0_remain = 0)) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "p" ) )) # Ptr  |-> p2)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (l22 = (cons (x) (l0)))) (PreH3 : (l2 = (app (l21) (l22)))) (PreH4 : (NonPos l21 )) (PreH5 : (p <> 0)) (PreH6 : (p2 <> 0)) (PreH7 : (retval <> 1)) (PreH8 : (retval = 0)) (PreH9 : (LP_implies l1 l2 )) (PreH10 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= (INT_MAX - 1 ))) (PreH15 : (BP0_upper = 0)) (PreH16 : (BP0_lower = 0)) (PreH17 : (BP0_remain = 0)) (PreH18 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_10 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (l22 = (cons (x) (l0)))) (PreH4 : (l2 = (app (l21) (l22)))) (PreH5 : (NonPos l21 )) (PreH6 : (p <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (retval <> 1)) (PreH9 : (retval = 0)) (PreH10 : (LP_implies l1 l2 )) (PreH11 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (n_pre >= 1)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0_upper = 0)) (PreH17 : (BP0_lower = 0)) (PreH18 : (BP0_remain = 0)) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_11 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (l22 = (cons (x) (l0)))) (PreH4 : (l2 = (app (l21) (l22)))) (PreH5 : (NonPos l21 )) (PreH6 : (p <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (retval <> 1)) (PreH9 : (retval = 0)) (PreH10 : (LP_implies l1 l2 )) (PreH11 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (n_pre >= 1)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0_upper = 0)) (PreH17 : (BP0_lower = 0)) (PreH18 : (BP0_remain = 0)) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_12 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Zlength (x)) = (n_pre + 1 ))) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (y <> 0)) (PreH4 : (h <> 0)) (PreH5 : (l22 = (cons (x) (l0)))) (PreH6 : (l2 = (app (l21) (l22)))) (PreH7 : (NonPos l21 )) (PreH8 : (p <> 0)) (PreH9 : (p2 <> 0)) (PreH10 : (retval <> 1)) (PreH11 : (retval = 0)) (PreH12 : (LP_implies l1 l2 )) (PreH13 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (n_pre >= 1)) (PreH17 : (n_pre <= (INT_MAX - 1 ))) (PreH18 : (BP0_upper = 0)) (PreH19 : (BP0_lower = 0)) (PreH20 : (BP0_remain = 0)) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lia_deduction_safety_wit_13 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (l22 = (cons (x) (l0)))) (PreH4 : (l2 = (app (l21) (l22)))) (PreH5 : (NonPos l21 )) (PreH6 : (p <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (retval <> 1)) (PreH9 : (retval = 0)) (PreH10 : (LP_implies l1 l2 )) (PreH11 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (n_pre >= 1)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0_upper = 0)) (PreH17 : (BP0_lower = 0)) (PreH18 : (BP0_remain = 0)) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "res" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_entail_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (PreH1 : (p2 <> 0)) (PreH2 : (retval <> 1)) (PreH3 : (retval = 0)) (PreH4 : (LP_implies l1 l2 )) (PreH5 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH6 : (BP0 <> 0)) (PreH7 : (pr_pre <> 0)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0_upper = 0)) (PreH11 : (BP0_lower = 0)) (PreH12 : (BP0_remain = 0)) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (l21: (@list Constraint))  (l22: (@list Constraint)) ,
  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (NonPos l21 ) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList_seg p2 p2 (n_pre + 1 ) l21 )
  **  (InequList p2 (n_pre + 1 ) l22 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (PreH1 : (p2 <> 0)) (PreH2 : (retval <> 1)) (PreH3 : (retval = 0)) (PreH4 : (LP_implies l1 l2 )) (PreH5 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH6 : (BP0 <> 0)) (PreH7 : (pr_pre <> 0)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0_upper = 0)) (PreH11 : (BP0_lower = 0)) (PreH12 : (BP0_remain = 0)) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  TT && emp 
|--
  “ (NonPos (@nil Constraint) ) ” 
  &&  “ (l2 = (app ((@nil Constraint)) (l2))) ”
  &&  emp
).

Definition lia_deduction_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (PreH1 : (p2 <> 0)) (PreH2 : (retval <> 1)) (PreH3 : (retval = 0)) (PreH4 : (LP_implies l1 l2 )) (PreH5 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH6 : (BP0 <> 0)) (PreH7 : (pr_pre <> 0)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0_upper = 0)) (PreH11 : (BP0_lower = 0)) (PreH12 : (BP0_remain = 0)) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (NonPos (@nil Constraint) )
.

Definition lia_deduction_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (PreH1 : (p2 <> 0)) (PreH2 : (retval <> 1)) (PreH3 : (retval = 0)) (PreH4 : (LP_implies l1 l2 )) (PreH5 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH6 : (BP0 <> 0)) (PreH7 : (pr_pre <> 0)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0_upper = 0)) (PreH11 : (BP0_lower = 0)) (PreH12 : (BP0_remain = 0)) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (l2 = (app ((@nil Constraint)) (l2)))
.

Definition lia_deduction_entail_wit_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21_2: (@list Constraint)) (l22_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Znth (0) (x) (0)) <= 0)) (PreH2 : (y <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l22_2 = (cons (x) (l0)))) (PreH5 : (l2 = (app (l21_2) (l22_2)))) (PreH6 : (NonPos l21_2 )) (PreH7 : (p <> 0)) (PreH8 : (p2 <> 0)) (PreH9 : (retval <> 1)) (PreH10 : (retval = 0)) (PreH11 : (LP_implies l1 l2 )) (PreH12 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (n_pre >= 1)) (PreH16 : (n_pre <= (INT_MAX - 1 ))) (PreH17 : (BP0_upper = 0)) (PreH18 : (BP0_lower = 0)) (PreH19 : (BP0_remain = 0)) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l21_2 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (l21: (@list Constraint))  (l22: (@list Constraint)) ,
  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (NonPos l21 ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList_seg p2 y (n_pre + 1 ) l21 )
  **  (InequList y (n_pre + 1 ) l22 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21_2: (@list Constraint)) (l22_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Znth (0) (x) (0)) <= 0)) (PreH2 : (y <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l22_2 = (cons (x) (l0)))) (PreH5 : (l2 = (app (l21_2) (l22_2)))) (PreH6 : (NonPos l21_2 )) (PreH7 : (p <> 0)) (PreH8 : (p2 <> 0)) (PreH9 : (retval <> 1)) (PreH10 : (retval = 0)) (PreH11 : (LP_implies l1 l2 )) (PreH12 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (n_pre >= 1)) (PreH16 : (n_pre <= (INT_MAX - 1 ))) (PreH17 : (BP0_upper = 0)) (PreH18 : (BP0_lower = 0)) (PreH19 : (BP0_remain = 0)) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l21_2 )
|--
  EX (l21: (@list Constraint)) ,
  “ (l2 = (app (l21) (l0))) ” 
  &&  “ (NonPos l21 ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList_seg p2 y (n_pre + 1 ) l21 )
).

Definition lia_deduction_return_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0_4: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2_3: Z) (l2_2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (l22 = (cons (x) (l0)))) (PreH4 : (l2_2 = (app (l21) (l22)))) (PreH5 : (NonPos l21 )) (PreH6 : (p <> 0)) (PreH7 : (p2_3 <> 0)) (PreH8 : (retval <> 1)) (PreH9 : (retval = 0)) (PreH10 : (LP_implies l1 l2_2 )) (PreH11 : (InequList_Zeros l2_2 1 (n_pre + 1 ) )) (PreH12 : (BP0_4 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (n_pre >= 1)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0_upper = 0)) (PreH17 : (BP0_lower = 0)) (PreH18 : (BP0_remain = 0)) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2_3 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0_4)
  **  ((pr_pre) # Ptr  |-> p2_3)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (BP0_3: Z)  (p2_2: Z)  (l2: (@list Constraint)) ,
  “ (0 = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ”
  &&  ((pr_pre) # Ptr  |-> p2_2)
  **  (InequList p2_2 (n_pre + 1 ) l2 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0_3)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0_4: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2_3: Z) (l2_2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (l22 = (cons (x) (l0)))) (PreH4 : (l2_2 = (app (l21) (l22)))) (PreH5 : (NonPos l21 )) (PreH6 : (p <> 0)) (PreH7 : (p2_3 <> 0)) (PreH8 : (retval <> 1)) (PreH9 : (retval = 0)) (PreH10 : (LP_implies l1 l2_2 )) (PreH11 : (InequList_Zeros l2_2 1 (n_pre + 1 ) )) (PreH12 : (BP0_4 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (n_pre >= 1)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0_upper = 0)) (PreH17 : (BP0_lower = 0)) (PreH18 : (BP0_remain = 0)) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2_3 p (n_pre + 1 ) l21 )
|--
  EX (h_2: Z)  (y_2: Z)  (l0_2: (@list Constraint))  (x_2: Constraint) ,
  “ (h_2 <> 0) ” 
  &&  “ (LP_implies l1 (cons (x_2) (l0_2)) ) ” 
  &&  “ (InequList_Zeros (cons (x_2) (l0_2)) 1 (n_pre + 1 ) ) ”
  &&  (InequList y_2 (n_pre + 1 ) l0_2 )
  **  ((&((p2_3)  # "InequList" ->ₛ "next")) # Ptr  |-> y_2)
  **  (coef_array h_2 (n_pre + 1 ) x_2 )
  **  ((&((p2_3)  # "InequList" ->ₛ "coef")) # Ptr  |-> h_2)
).

Definition lia_deduction_return_wit_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0_4: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2_3: Z) (l2_2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Zlength (x)) = (n_pre + 1 ))) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (y <> 0)) (PreH4 : (h <> 0)) (PreH5 : (l22 = (cons (x) (l0)))) (PreH6 : (l2_2 = (app (l21) (l22)))) (PreH7 : (NonPos l21 )) (PreH8 : (p <> 0)) (PreH9 : (p2_3 <> 0)) (PreH10 : (retval <> 1)) (PreH11 : (retval = 0)) (PreH12 : (LP_implies l1 l2_2 )) (PreH13 : (InequList_Zeros l2_2 1 (n_pre + 1 ) )) (PreH14 : (BP0_4 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (n_pre >= 1)) (PreH17 : (n_pre <= (INT_MAX - 1 ))) (PreH18 : (BP0_upper = 0)) (PreH19 : (BP0_lower = 0)) (PreH20 : (BP0_remain = 0)) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0_4)
  **  ((pr_pre) # Ptr  |-> p2_3)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (BP0_2: Z)  (p2: Z) ,
  “ (1 = 1) ” 
  &&  “ (UNSAT l1 ) ”
  &&  ((pr_pre) # Ptr  |-> p2)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0_4: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2_3: Z) (l2_2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Zlength (x)) = (n_pre + 1 ))) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (y <> 0)) (PreH4 : (h <> 0)) (PreH5 : (l22 = (cons (x) (l0)))) (PreH6 : (l2_2 = (app (l21) (l22)))) (PreH7 : (NonPos l21 )) (PreH8 : (p <> 0)) (PreH9 : (p2_3 <> 0)) (PreH10 : (retval <> 1)) (PreH11 : (retval = 0)) (PreH12 : (LP_implies l1 l2_2 )) (PreH13 : (InequList_Zeros l2_2 1 (n_pre + 1 ) )) (PreH14 : (BP0_4 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (n_pre >= 1)) (PreH17 : (n_pre <= (INT_MAX - 1 ))) (PreH18 : (BP0_upper = 0)) (PreH19 : (BP0_lower = 0)) (PreH20 : (BP0_remain = 0)) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  TT && emp 
|--
  “ (UNSAT l1 ) ”
  &&  emp
).

Definition lia_deduction_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0_4: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2_3: Z) (l2_2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Zlength (x)) = (n_pre + 1 ))) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (y <> 0)) (PreH4 : (h <> 0)) (PreH5 : (l22 = (cons (x) (l0)))) (PreH6 : (l2_2 = (app (l21) (l22)))) (PreH7 : (NonPos l21 )) (PreH8 : (p <> 0)) (PreH9 : (p2_3 <> 0)) (PreH10 : (retval <> 1)) (PreH11 : (retval = 0)) (PreH12 : (LP_implies l1 l2_2 )) (PreH13 : (InequList_Zeros l2_2 1 (n_pre + 1 ) )) (PreH14 : (BP0_4 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (n_pre >= 1)) (PreH17 : (n_pre <= (INT_MAX - 1 ))) (PreH18 : (BP0_upper = 0)) (PreH19 : (BP0_lower = 0)) (PreH20 : (BP0_remain = 0)) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (UNSAT l1 )
.

Definition lia_deduction_return_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0_4: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (p2_3: Z) (l2_2: (@list Constraint)) (retval: Z) (PreH1 : (p2_3 = 0)) (PreH2 : (retval <> 1)) (PreH3 : (retval = 0)) (PreH4 : (LP_implies l1 l2_2 )) (PreH5 : (InequList_Zeros l2_2 1 (n_pre + 1 ) )) (PreH6 : (BP0_4 <> 0)) (PreH7 : (pr_pre <> 0)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0_upper = 0)) (PreH11 : (BP0_lower = 0)) (PreH12 : (BP0_remain = 0)) (PreH13 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0_4)
  **  ((pr_pre) # Ptr  |-> p2_3)
  **  (InequList p2_3 (n_pre + 1 ) l2_2 )
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (BP0_3: Z)  (p2_2: Z)  (l2: (@list Constraint)) ,
  “ (0 = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ”
  &&  ((pr_pre) # Ptr  |-> p2_2)
  **  (InequList p2_2 (n_pre + 1 ) l2 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0_3)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition lia_deduction_return_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0_4: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = 1)) (PreH3 : (BP0_4 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) (PreH10 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0_4)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (BP0: Z) ,
  “ ((-1) = (-1)) ”
  &&  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition lia_deduction_partial_solve_wit_1_pure := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= (INT_MAX - 1 ))) (PreH5 : (BP0_upper = 0)) (PreH6 : (BP0_lower = 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "res" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList p1 (n_pre + 1 ) l1 )
|--
  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
.

Definition lia_deduction_partial_solve_wit_1_aux := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= (INT_MAX - 1 ))) (PreH5 : (BP0_upper = 0)) (PreH6 : (BP0_lower = 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList p1 (n_pre + 1 ) l1 )
|--
  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> 0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> 0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> 0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList p1 (n_pre + 1 ) l1 )
.

Definition lia_deduction_partial_solve_wit_1 := lia_deduction_partial_solve_wit_1_pure -> lia_deduction_partial_solve_wit_1_aux.

Definition lia_deduction_partial_solve_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (PreH1 : (l2 = (app (l21) (l22)))) (PreH2 : (NonPos l21 )) (PreH3 : (p <> 0)) (PreH4 : (p2 <> 0)) (PreH5 : (retval <> 1)) (PreH6 : (retval = 0)) (PreH7 : (LP_implies l1 l2 )) (PreH8 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0_upper = 0)) (PreH14 : (BP0_lower = 0)) (PreH15 : (BP0_remain = 0)) (PreH16 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  (InequList p (n_pre + 1 ) l22 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (h: Z)  (y: Z)  (l0: (@list Constraint))  (x: Constraint) ,
  “ (h <> 0) ” 
  &&  “ (l22 = (cons (x) (l0))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (NonPos l21 ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition lia_deduction_partial_solve_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (l22 = (cons (x) (l0)))) (PreH4 : (l2 = (app (l21) (l22)))) (PreH5 : (NonPos l21 )) (PreH6 : (p <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (retval <> 1)) (PreH9 : (retval = 0)) (PreH10 : (LP_implies l1 l2 )) (PreH11 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) (PreH14 : (n_pre >= 1)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0_upper = 0)) (PreH17 : (BP0_lower = 0)) (PreH18 : (BP0_remain = 0)) (PreH19 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  “ (y <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l22 = (cons (x) (l0))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (NonPos l21 ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (((h + (0 * sizeof(INT)))) # Int  |-> (coef_Znth (0) (x) (0)))
  **  (coef_array_missing_i_rec h 0 0 (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition lia_deduction_partial_solve_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Znth (0) (x) (0)) > 0)) (PreH2 : (y <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l22 = (cons (x) (l0)))) (PreH5 : (l2 = (app (l21) (l22)))) (PreH6 : (NonPos l21 )) (PreH7 : (p <> 0)) (PreH8 : (p2 <> 0)) (PreH9 : (retval <> 1)) (PreH10 : (retval = 0)) (PreH11 : (LP_implies l1 l2 )) (PreH12 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) (PreH15 : (n_pre >= 1)) (PreH16 : (n_pre <= (INT_MAX - 1 ))) (PreH17 : (BP0_upper = 0)) (PreH18 : (BP0_lower = 0)) (PreH19 : (BP0_remain = 0)) (PreH20 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  “ ((coef_Znth (0) (x) (0)) > 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l22 = (cons (x) (l0))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (NonPos l21 ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList_seg p2 p (n_pre + 1 ) l21 )
  **  (InequList p (n_pre + 1 ) (cons (x) (l0)) )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition lia_deduction_partial_solve_wit_5 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (retval: Z) (p2: Z) (l2: (@list Constraint)) (p: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : ((coef_Zlength (x)) = (n_pre + 1 ))) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (y <> 0)) (PreH4 : (h <> 0)) (PreH5 : (l22 = (cons (x) (l0)))) (PreH6 : (l2 = (app (l21) (l22)))) (PreH7 : (NonPos l21 )) (PreH8 : (p <> 0)) (PreH9 : (p2 <> 0)) (PreH10 : (retval <> 1)) (PreH11 : (retval = 0)) (PreH12 : (LP_implies l1 l2 )) (PreH13 : (InequList_Zeros l2 1 (n_pre + 1 ) )) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) (PreH16 : (n_pre >= 1)) (PreH17 : (n_pre <= (INT_MAX - 1 ))) (PreH18 : (BP0_upper = 0)) (PreH19 : (BP0_lower = 0)) (PreH20 : (BP0_remain = 0)) (PreH21 : (LP_abs_in_int_range (n_pre + 1 ) l1 )) ,
  (InequList p2 (n_pre + 1 ) (app (l21) ((cons (x) (l0)))) )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  “ ((coef_Zlength (x)) = (n_pre + 1 )) ” 
  &&  “ ((coef_Znth (0) (x) (0)) > 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l22 = (cons (x) (l0))) ” 
  &&  “ (l2 = (app (l21) (l22))) ” 
  &&  “ (NonPos l21 ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (LP_implies l1 l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (LP_abs_in_int_range (n_pre + 1 ) l1 ) ”
  &&  (InequList p2 (n_pre + 1 ) (app (l21) ((cons (x) (l0)))) )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition lia_deduction_which_implies_wit_1 := 
(
forall (n_pre: Z) (p2: Z) (l20: (@list Constraint)) (x: Constraint) (l10: (@list Constraint)) (p: Z) ,
  (InequList_seg p2 p (n_pre + 1 ) l10 )
  **  (InequList p (n_pre + 1 ) (cons (x) (l20)) )
|--
  “ ((coef_Zlength (x)) = (n_pre + 1 )) ”
  &&  (InequList p2 (n_pre + 1 ) (app (l10) ((cons (x) (l20)))) )
) \/
(
forall (n_pre: Z) (p2: Z) (l20: (@list Constraint)) (x: Constraint) (l10: (@list Constraint)) (p: Z) (y: Z) (h: Z) (PreH1 : (h <> 0)) ,
  (InequList y (n_pre + 1 ) l20 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l10 )
|--
  “ ((coef_Zlength (x)) = (n_pre + 1 )) ”
  &&  (InequList p2 (n_pre + 1 ) (app (l10) ((cons (x) (l20)))) )
).

Definition lia_deduction_which_implies_wit_1_split_goal_1 := 
forall (n_pre: Z) (p2: Z) (l20: (@list Constraint)) (x: Constraint) (l10: (@list Constraint)) (p: Z) (y: Z) (h: Z) (PreH1 : (h <> 0)) ,
  (InequList y (n_pre + 1 ) l20 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l10 )
|--
  “ ((coef_Zlength (x)) = (n_pre + 1 )) ”
.

Definition lia_deduction_which_implies_wit_1_split_goal_spatial := 
forall (n_pre: Z) (p2: Z) (l20: (@list Constraint)) (x: Constraint) (l10: (@list Constraint)) (p: Z) (y: Z) (h: Z) (PreH1 : (h <> 0)) ,
  (InequList y (n_pre + 1 ) l20 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg p2 p (n_pre + 1 ) l10 )
|--
  (InequList p2 (n_pre + 1 ) (app (l10) ((cons (x) (l20)))) )
.

Module Type VC_Correct.

Include fme_Strategy_Correct.

Axiom proof_of_gcd_safety_wit_1 : gcd_safety_wit_1.
Axiom proof_of_gcd_safety_wit_2 : gcd_safety_wit_2.
Axiom proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Axiom proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Axiom proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure.
Axiom proof_of_gcd_partial_solve_wit_1 : gcd_partial_solve_wit_1.
Axiom proof_of_check_add_safe_safety_wit_1 : check_add_safe_safety_wit_1.
Axiom proof_of_check_add_safe_safety_wit_2 : check_add_safe_safety_wit_2.
Axiom proof_of_check_add_safe_safety_wit_3 : check_add_safe_safety_wit_3.
Axiom proof_of_check_add_safe_safety_wit_4 : check_add_safe_safety_wit_4.
Axiom proof_of_check_add_safe_safety_wit_5 : check_add_safe_safety_wit_5.
Axiom proof_of_check_add_safe_safety_wit_6 : check_add_safe_safety_wit_6.
Axiom proof_of_check_add_safe_return_wit_1 : check_add_safe_return_wit_1.
Axiom proof_of_check_add_safe_return_wit_2 : check_add_safe_return_wit_2.
Axiom proof_of_check_add_safe_return_wit_3 : check_add_safe_return_wit_3.
Axiom proof_of_check_add_safe_return_wit_4 : check_add_safe_return_wit_4.
Axiom proof_of_NilInequList_safety_wit_1 : NilInequList_safety_wit_1.
Axiom proof_of_NilInequList_return_wit_1 : NilInequList_return_wit_1.
Axiom proof_of_ConsInequList_return_wit_1 : ConsInequList_return_wit_1.
Axiom proof_of_ConsInequList_partial_solve_wit_1 : ConsInequList_partial_solve_wit_1.
Axiom proof_of_free_InequList_safety_wit_1 : free_InequList_safety_wit_1.
Axiom proof_of_free_InequList_safety_wit_2 : free_InequList_safety_wit_2.
Axiom proof_of_free_InequList_safety_wit_3 : free_InequList_safety_wit_3.
Axiom proof_of_free_InequList_safety_wit_4 : free_InequList_safety_wit_4.
Axiom proof_of_free_InequList_return_wit_1 : free_InequList_return_wit_1.
Axiom proof_of_free_InequList_return_wit_2 : free_InequList_return_wit_2.
Axiom proof_of_free_InequList_return_wit_3 : free_InequList_return_wit_3.
Axiom proof_of_free_InequList_partial_solve_wit_1 : free_InequList_partial_solve_wit_1.
Axiom proof_of_free_InequList_partial_solve_wit_2 : free_InequList_partial_solve_wit_2.
Axiom proof_of_free_InequList_partial_solve_wit_3 : free_InequList_partial_solve_wit_3.
Axiom proof_of_free_InequList_partial_solve_wit_4 : free_InequList_partial_solve_wit_4.
Axiom proof_of_free_InequList_partial_solve_wit_5 : free_InequList_partial_solve_wit_5.
Axiom proof_of_eliminate_safety_wit_1 : eliminate_safety_wit_1.
Axiom proof_of_eliminate_safety_wit_2 : eliminate_safety_wit_2.
Axiom proof_of_eliminate_safety_wit_3 : eliminate_safety_wit_3.
Axiom proof_of_eliminate_entail_wit_1 : eliminate_entail_wit_1.
Axiom proof_of_eliminate_entail_wit_2 : eliminate_entail_wit_2.
Axiom proof_of_eliminate_entail_wit_3_1 : eliminate_entail_wit_3_1.
Axiom proof_of_eliminate_entail_wit_3_2 : eliminate_entail_wit_3_2.
Axiom proof_of_eliminate_entail_wit_3_3 : eliminate_entail_wit_3_3.
Axiom proof_of_eliminate_return_wit_1 : eliminate_return_wit_1.
Axiom proof_of_eliminate_partial_solve_wit_1 : eliminate_partial_solve_wit_1.
Axiom proof_of_eliminate_partial_solve_wit_2 : eliminate_partial_solve_wit_2.
Axiom proof_of_eliminate_partial_solve_wit_3 : eliminate_partial_solve_wit_3.
Axiom proof_of_eliminate_partial_solve_wit_4_pure : eliminate_partial_solve_wit_4_pure.
Axiom proof_of_eliminate_partial_solve_wit_4 : eliminate_partial_solve_wit_4.
Axiom proof_of_eliminate_partial_solve_wit_5 : eliminate_partial_solve_wit_5.
Axiom proof_of_eliminate_partial_solve_wit_6 : eliminate_partial_solve_wit_6.
Axiom proof_of_eliminate_which_implies_wit_1 : eliminate_which_implies_wit_1.
Axiom proof_of_generate_new_constr_safety_wit_1 : generate_new_constr_safety_wit_1.
Axiom proof_of_generate_new_constr_safety_wit_2 : generate_new_constr_safety_wit_2.
Axiom proof_of_generate_new_constr_safety_wit_3 : generate_new_constr_safety_wit_3.
Axiom proof_of_generate_new_constr_safety_wit_4 : generate_new_constr_safety_wit_4.
Axiom proof_of_generate_new_constr_safety_wit_5 : generate_new_constr_safety_wit_5.
Axiom proof_of_generate_new_constr_safety_wit_6 : generate_new_constr_safety_wit_6.
Axiom proof_of_generate_new_constr_safety_wit_7 : generate_new_constr_safety_wit_7.
Axiom proof_of_generate_new_constr_safety_wit_8 : generate_new_constr_safety_wit_8.
Axiom proof_of_generate_new_constr_safety_wit_9 : generate_new_constr_safety_wit_9.
Axiom proof_of_generate_new_constr_safety_wit_10 : generate_new_constr_safety_wit_10.
Axiom proof_of_generate_new_constr_safety_wit_11 : generate_new_constr_safety_wit_11.
Axiom proof_of_generate_new_constr_safety_wit_12 : generate_new_constr_safety_wit_12.
Axiom proof_of_generate_new_constr_safety_wit_13 : generate_new_constr_safety_wit_13.
Axiom proof_of_generate_new_constr_safety_wit_14 : generate_new_constr_safety_wit_14.
Axiom proof_of_generate_new_constr_safety_wit_15 : generate_new_constr_safety_wit_15.
Axiom proof_of_generate_new_constr_safety_wit_16 : generate_new_constr_safety_wit_16.
Axiom proof_of_generate_new_constr_safety_wit_17 : generate_new_constr_safety_wit_17.
Axiom proof_of_generate_new_constr_safety_wit_18 : generate_new_constr_safety_wit_18.
Axiom proof_of_generate_new_constr_safety_wit_19 : generate_new_constr_safety_wit_19.
Axiom proof_of_generate_new_constr_safety_wit_20 : generate_new_constr_safety_wit_20.
Axiom proof_of_generate_new_constr_safety_wit_21 : generate_new_constr_safety_wit_21.
Axiom proof_of_generate_new_constr_safety_wit_22 : generate_new_constr_safety_wit_22.
Axiom proof_of_generate_new_constr_safety_wit_23 : generate_new_constr_safety_wit_23.
Axiom proof_of_generate_new_constr_safety_wit_24 : generate_new_constr_safety_wit_24.
Axiom proof_of_generate_new_constr_safety_wit_25 : generate_new_constr_safety_wit_25.
Axiom proof_of_generate_new_constr_safety_wit_26 : generate_new_constr_safety_wit_26.
Axiom proof_of_generate_new_constr_safety_wit_27 : generate_new_constr_safety_wit_27.
Axiom proof_of_generate_new_constr_safety_wit_28 : generate_new_constr_safety_wit_28.
Axiom proof_of_generate_new_constr_safety_wit_29 : generate_new_constr_safety_wit_29.
Axiom proof_of_generate_new_constr_safety_wit_30 : generate_new_constr_safety_wit_30.
Axiom proof_of_generate_new_constr_entail_wit_1 : generate_new_constr_entail_wit_1.
Axiom proof_of_generate_new_constr_entail_wit_2 : generate_new_constr_entail_wit_2.
Axiom proof_of_generate_new_constr_entail_wit_3 : generate_new_constr_entail_wit_3.
Axiom proof_of_generate_new_constr_entail_wit_4 : generate_new_constr_entail_wit_4.
Axiom proof_of_generate_new_constr_entail_wit_5 : generate_new_constr_entail_wit_5.
Axiom proof_of_generate_new_constr_return_wit_1 : generate_new_constr_return_wit_1.
Axiom proof_of_generate_new_constr_return_wit_2 : generate_new_constr_return_wit_2.
Axiom proof_of_generate_new_constr_return_wit_3 : generate_new_constr_return_wit_3.
Axiom proof_of_generate_new_constr_return_wit_4 : generate_new_constr_return_wit_4.
Axiom proof_of_generate_new_constr_return_wit_5 : generate_new_constr_return_wit_5.
Axiom proof_of_generate_new_constr_return_wit_6 : generate_new_constr_return_wit_6.
Axiom proof_of_generate_new_constr_partial_solve_wit_1 : generate_new_constr_partial_solve_wit_1.
Axiom proof_of_generate_new_constr_partial_solve_wit_2 : generate_new_constr_partial_solve_wit_2.
Axiom proof_of_generate_new_constr_partial_solve_wit_3_pure : generate_new_constr_partial_solve_wit_3_pure.
Axiom proof_of_generate_new_constr_partial_solve_wit_3 : generate_new_constr_partial_solve_wit_3.
Axiom proof_of_generate_new_constr_partial_solve_wit_4 : generate_new_constr_partial_solve_wit_4.
Axiom proof_of_generate_new_constr_partial_solve_wit_5 : generate_new_constr_partial_solve_wit_5.
Axiom proof_of_generate_new_constr_partial_solve_wit_6 : generate_new_constr_partial_solve_wit_6.
Axiom proof_of_generate_new_constr_partial_solve_wit_7 : generate_new_constr_partial_solve_wit_7.
Axiom proof_of_generate_new_constr_partial_solve_wit_8 : generate_new_constr_partial_solve_wit_8.
Axiom proof_of_generate_new_constr_partial_solve_wit_9 : generate_new_constr_partial_solve_wit_9.
Axiom proof_of_generate_new_constr_partial_solve_wit_10 : generate_new_constr_partial_solve_wit_10.
Axiom proof_of_generate_new_constr_partial_solve_wit_11_pure : generate_new_constr_partial_solve_wit_11_pure.
Axiom proof_of_generate_new_constr_partial_solve_wit_11 : generate_new_constr_partial_solve_wit_11.
Axiom proof_of_generate_new_constr_partial_solve_wit_12 : generate_new_constr_partial_solve_wit_12.
Axiom proof_of_generate_new_constr_partial_solve_wit_13 : generate_new_constr_partial_solve_wit_13.
Axiom proof_of_generate_new_constraint_list_safety_wit_1 : generate_new_constraint_list_safety_wit_1.
Axiom proof_of_generate_new_constraint_list_safety_wit_2 : generate_new_constraint_list_safety_wit_2.
Axiom proof_of_generate_new_constraint_list_safety_wit_3 : generate_new_constraint_list_safety_wit_3.
Axiom proof_of_generate_new_constraint_list_safety_wit_4 : generate_new_constraint_list_safety_wit_4.
Axiom proof_of_generate_new_constraint_list_safety_wit_5 : generate_new_constraint_list_safety_wit_5.
Axiom proof_of_generate_new_constraint_list_safety_wit_6 : generate_new_constraint_list_safety_wit_6.
Axiom proof_of_generate_new_constraint_list_safety_wit_7 : generate_new_constraint_list_safety_wit_7.
Axiom proof_of_generate_new_constraint_list_entail_wit_1 : generate_new_constraint_list_entail_wit_1.
Axiom proof_of_generate_new_constraint_list_entail_wit_2 : generate_new_constraint_list_entail_wit_2.
Axiom proof_of_generate_new_constraint_list_entail_wit_3 : generate_new_constraint_list_entail_wit_3.
Axiom proof_of_generate_new_constraint_list_entail_wit_4 : generate_new_constraint_list_entail_wit_4.
Axiom proof_of_generate_new_constraint_list_return_wit_1 : generate_new_constraint_list_return_wit_1.
Axiom proof_of_generate_new_constraint_list_return_wit_2 : generate_new_constraint_list_return_wit_2.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_1_pure : generate_new_constraint_list_partial_solve_wit_1_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_1 : generate_new_constraint_list_partial_solve_wit_1.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_2_pure : generate_new_constraint_list_partial_solve_wit_2_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_2 : generate_new_constraint_list_partial_solve_wit_2.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_3_pure : generate_new_constraint_list_partial_solve_wit_3_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_3 : generate_new_constraint_list_partial_solve_wit_3.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_4 : generate_new_constraint_list_partial_solve_wit_4.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_5_pure : generate_new_constraint_list_partial_solve_wit_5_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_5 : generate_new_constraint_list_partial_solve_wit_5.
Axiom proof_of_generate_new_constraint_list_which_implies_wit_1 : generate_new_constraint_list_which_implies_wit_1.
Axiom proof_of_generate_new_constraint_list_which_implies_wit_2 : generate_new_constraint_list_which_implies_wit_2.
Axiom proof_of_real_shadow_safety_wit_1 : real_shadow_safety_wit_1.
Axiom proof_of_real_shadow_safety_wit_2 : real_shadow_safety_wit_2.
Axiom proof_of_real_shadow_safety_wit_3 : real_shadow_safety_wit_3.
Axiom proof_of_real_shadow_safety_wit_4 : real_shadow_safety_wit_4.
Axiom proof_of_real_shadow_safety_wit_5 : real_shadow_safety_wit_5.
Axiom proof_of_real_shadow_safety_wit_6 : real_shadow_safety_wit_6.
Axiom proof_of_real_shadow_safety_wit_7 : real_shadow_safety_wit_7.
Axiom proof_of_real_shadow_safety_wit_8 : real_shadow_safety_wit_8.
Axiom proof_of_real_shadow_safety_wit_9 : real_shadow_safety_wit_9.
Axiom proof_of_real_shadow_safety_wit_10 : real_shadow_safety_wit_10.
Axiom proof_of_real_shadow_safety_wit_11 : real_shadow_safety_wit_11.
Axiom proof_of_real_shadow_safety_wit_12 : real_shadow_safety_wit_12.
Axiom proof_of_real_shadow_safety_wit_13 : real_shadow_safety_wit_13.
Axiom proof_of_real_shadow_safety_wit_14 : real_shadow_safety_wit_14.
Axiom proof_of_real_shadow_safety_wit_15 : real_shadow_safety_wit_15.
Axiom proof_of_real_shadow_safety_wit_16 : real_shadow_safety_wit_16.
Axiom proof_of_real_shadow_safety_wit_17 : real_shadow_safety_wit_17.
Axiom proof_of_real_shadow_safety_wit_18 : real_shadow_safety_wit_18.
Axiom proof_of_real_shadow_safety_wit_19 : real_shadow_safety_wit_19.
Axiom proof_of_real_shadow_safety_wit_20 : real_shadow_safety_wit_20.
Axiom proof_of_real_shadow_safety_wit_21 : real_shadow_safety_wit_21.
Axiom proof_of_real_shadow_safety_wit_22 : real_shadow_safety_wit_22.
Axiom proof_of_real_shadow_safety_wit_23 : real_shadow_safety_wit_23.
Axiom proof_of_real_shadow_safety_wit_24 : real_shadow_safety_wit_24.
Axiom proof_of_real_shadow_safety_wit_25 : real_shadow_safety_wit_25.
Axiom proof_of_real_shadow_entail_wit_1 : real_shadow_entail_wit_1.
Axiom proof_of_real_shadow_entail_wit_2_1 : real_shadow_entail_wit_2_1.
Axiom proof_of_real_shadow_entail_wit_2_2 : real_shadow_entail_wit_2_2.
Axiom proof_of_real_shadow_return_wit_1 : real_shadow_return_wit_1.
Axiom proof_of_real_shadow_return_wit_2 : real_shadow_return_wit_2.
Axiom proof_of_real_shadow_return_wit_3 : real_shadow_return_wit_3.
Axiom proof_of_real_shadow_return_wit_4 : real_shadow_return_wit_4.
Axiom proof_of_real_shadow_return_wit_5 : real_shadow_return_wit_5.
Axiom proof_of_real_shadow_return_wit_6 : real_shadow_return_wit_6.
Axiom proof_of_real_shadow_return_wit_7 : real_shadow_return_wit_7.
Axiom proof_of_real_shadow_partial_solve_wit_1_pure : real_shadow_partial_solve_wit_1_pure.
Axiom proof_of_real_shadow_partial_solve_wit_1 : real_shadow_partial_solve_wit_1.
Axiom proof_of_real_shadow_partial_solve_wit_2 : real_shadow_partial_solve_wit_2.
Axiom proof_of_real_shadow_partial_solve_wit_3 : real_shadow_partial_solve_wit_3.
Axiom proof_of_real_shadow_partial_solve_wit_4_pure : real_shadow_partial_solve_wit_4_pure.
Axiom proof_of_real_shadow_partial_solve_wit_4 : real_shadow_partial_solve_wit_4.
Axiom proof_of_real_shadow_partial_solve_wit_5_pure : real_shadow_partial_solve_wit_5_pure.
Axiom proof_of_real_shadow_partial_solve_wit_5 : real_shadow_partial_solve_wit_5.
Axiom proof_of_real_shadow_partial_solve_wit_6 : real_shadow_partial_solve_wit_6.
Axiom proof_of_real_shadow_partial_solve_wit_7 : real_shadow_partial_solve_wit_7.
Axiom proof_of_real_shadow_partial_solve_wit_8 : real_shadow_partial_solve_wit_8.
Axiom proof_of_real_shadow_partial_solve_wit_9 : real_shadow_partial_solve_wit_9.
Axiom proof_of_real_shadow_partial_solve_wit_10 : real_shadow_partial_solve_wit_10.
Axiom proof_of_real_shadow_partial_solve_wit_11 : real_shadow_partial_solve_wit_11.
Axiom proof_of_real_shadow_partial_solve_wit_12 : real_shadow_partial_solve_wit_12.
Axiom proof_of_real_shadow_partial_solve_wit_13 : real_shadow_partial_solve_wit_13.
Axiom proof_of_lia_deduction_safety_wit_1 : lia_deduction_safety_wit_1.
Axiom proof_of_lia_deduction_safety_wit_2 : lia_deduction_safety_wit_2.
Axiom proof_of_lia_deduction_safety_wit_3 : lia_deduction_safety_wit_3.
Axiom proof_of_lia_deduction_safety_wit_4 : lia_deduction_safety_wit_4.
Axiom proof_of_lia_deduction_safety_wit_5 : lia_deduction_safety_wit_5.
Axiom proof_of_lia_deduction_safety_wit_6 : lia_deduction_safety_wit_6.
Axiom proof_of_lia_deduction_safety_wit_7 : lia_deduction_safety_wit_7.
Axiom proof_of_lia_deduction_safety_wit_8 : lia_deduction_safety_wit_8.
Axiom proof_of_lia_deduction_safety_wit_9 : lia_deduction_safety_wit_9.
Axiom proof_of_lia_deduction_safety_wit_10 : lia_deduction_safety_wit_10.
Axiom proof_of_lia_deduction_safety_wit_11 : lia_deduction_safety_wit_11.
Axiom proof_of_lia_deduction_safety_wit_12 : lia_deduction_safety_wit_12.
Axiom proof_of_lia_deduction_safety_wit_13 : lia_deduction_safety_wit_13.
Axiom proof_of_lia_deduction_entail_wit_1 : lia_deduction_entail_wit_1.
Axiom proof_of_lia_deduction_entail_wit_2 : lia_deduction_entail_wit_2.
Axiom proof_of_lia_deduction_return_wit_1 : lia_deduction_return_wit_1.
Axiom proof_of_lia_deduction_return_wit_2 : lia_deduction_return_wit_2.
Axiom proof_of_lia_deduction_return_wit_3 : lia_deduction_return_wit_3.
Axiom proof_of_lia_deduction_return_wit_4 : lia_deduction_return_wit_4.
Axiom proof_of_lia_deduction_partial_solve_wit_1_pure : lia_deduction_partial_solve_wit_1_pure.
Axiom proof_of_lia_deduction_partial_solve_wit_1 : lia_deduction_partial_solve_wit_1.
Axiom proof_of_lia_deduction_partial_solve_wit_2 : lia_deduction_partial_solve_wit_2.
Axiom proof_of_lia_deduction_partial_solve_wit_3 : lia_deduction_partial_solve_wit_3.
Axiom proof_of_lia_deduction_partial_solve_wit_4 : lia_deduction_partial_solve_wit_4.
Axiom proof_of_lia_deduction_partial_solve_wit_5 : lia_deduction_partial_solve_wit_5.
Axiom proof_of_lia_deduction_which_implies_wit_1 : lia_deduction_which_implies_wit_1.

End VC_Correct.
