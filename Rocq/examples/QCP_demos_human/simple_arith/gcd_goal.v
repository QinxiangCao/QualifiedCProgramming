From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function gcd -----*)

Definition gcd_safety_wit_1 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (y_pre <= INT_MAX)) (PreH3 : (y_pre >= INT_MIN)) (PreH4 : (INT_MIN < x_pre)) (PreH5 : (INT_MIN < y_pre)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gcd_safety_wit_2 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ ((x_pre <> (INT_MIN)) \/ (y_pre <> (-1))) ”
  &&  “ (y_pre <> 0) ”
.

Definition gcd_entail_wit_1 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (INT_MIN < y_pre)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (x_pre <= INT_MAX) ”
  &&  “ (y_pre <= INT_MAX) ”
  &&  “ (y_pre >= INT_MIN) ”
  &&  “ (INT_MIN < x_pre) ”
  &&  “ (INT_MIN < y_pre) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
.

Definition gcd_return_wit_1 :=
(
forall (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zgcd (y_pre) ((x_pre % ( y_pre ) ))))) (PreH2 : (y_pre <> 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) (y_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zgcd (y_pre) ((x_pre % ( y_pre ) ))))) (PreH2 : (y_pre <> 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) (y_pre))) ”
  &&  emp
).

Definition gcd_return_wit_1_split_goal_1 :=
forall (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zgcd (y_pre) ((x_pre % ( y_pre ) ))))) (PreH2 : (y_pre <> 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  (retval = (Zgcd (x_pre) (y_pre)))
.

Definition gcd_return_wit_2 :=
(
forall (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (y_pre = 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) (y_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (y_pre = 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  TT && emp 
|--
  “ (retval = (Zgcd (x_pre) (0))) ”
  &&  emp
).

Definition gcd_return_wit_2_split_goal_1 :=
forall (x_pre: Z) (y_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (y_pre = 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  (retval = (Zgcd (x_pre) (0)))
.

Definition gcd_partial_solve_wit_1_pure :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (y_pre = 0)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (INT_MIN < x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
.

Definition gcd_partial_solve_wit_1_aux :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (y_pre = 0)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)),
  TT && emp 
|--
  “ (INT_MIN < x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ (y_pre = 0) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ (y_pre <= INT_MAX) ”
  &&  “ (y_pre >= INT_MIN) ”
  &&  “ (INT_MIN < x_pre) ”
  &&  “ (INT_MIN < y_pre) ”
  &&  emp
.

Definition gcd_partial_solve_wit_1 := gcd_partial_solve_wit_1_pure -> gcd_partial_solve_wit_1_aux.

Definition gcd_partial_solve_wit_2_pure :=
(
forall (x_pre: Z) (y_pre: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (INT_MIN < y_pre) ”
  &&  “ (INT_MIN < (x_pre % ( y_pre ) )) ”
) \/
(
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre >= INT_MIN)) (PreH2 : (y_pre <> 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (INT_MIN < (x_pre % ( y_pre ) )) ”
).

Definition gcd_partial_solve_wit_2_pure_split_goal_1 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre >= INT_MIN)) (PreH2 : (y_pre <> 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (INT_MIN < (x_pre % ( y_pre ) )) ”
.

Definition gcd_partial_solve_wit_2_aux :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)),
  TT && emp 
|--
  “ (INT_MIN < y_pre) ”
  &&  “ (INT_MIN < (x_pre % ( y_pre ) )) ”
  &&  “ (y_pre <> 0) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ (y_pre <= INT_MAX) ”
  &&  “ (y_pre >= INT_MIN) ”
  &&  “ (INT_MIN < x_pre) ”
  &&  “ (INT_MIN < y_pre) ”
  &&  emp
.

Definition gcd_partial_solve_wit_2 := gcd_partial_solve_wit_2_pure -> gcd_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_gcd_safety_wit_1 : gcd_safety_wit_1.
Axiom proof_of_gcd_safety_wit_2 : gcd_safety_wit_2.
Axiom proof_of_gcd_entail_wit_1 : gcd_entail_wit_1.
Axiom proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Axiom proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Axiom proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure.
Axiom proof_of_gcd_partial_solve_wit_1 : gcd_partial_solve_wit_1.
Axiom proof_of_gcd_partial_solve_wit_2_pure : gcd_partial_solve_wit_2_pure.
Axiom proof_of_gcd_partial_solve_wit_2 : gcd_partial_solve_wit_2.

End VC_Correct.
