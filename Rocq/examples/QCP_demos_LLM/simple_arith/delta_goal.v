From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function delta -----*)

Definition delta_safety_wit_1 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ ((y_pre - x_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (y_pre - x_pre )) ”
.

Definition delta_safety_wit_2 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ ((x_pre - y_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x_pre - y_pre )) ”
.

Definition delta_return_wit_1 :=
(
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  TT && emp 
|--
  “ ((x_pre - y_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  TT && emp 
|--
  “ ((x_pre - y_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
).

Definition delta_return_wit_1_split_goal_1 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  ((x_pre - y_pre ) = (Z.abs ((x_pre - y_pre ))))
.

Definition delta_return_wit_2 :=
(
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  TT && emp 
|--
  “ ((y_pre - x_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  TT && emp 
|--
  “ ((y_pre - x_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
).

Definition delta_return_wit_2_split_goal_1 :=
forall (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)),
  ((y_pre - x_pre ) = (Z.abs ((x_pre - y_pre ))))
.

Module Type VC_Correct.


Axiom proof_of_delta_safety_wit_1 : delta_safety_wit_1.
Axiom proof_of_delta_safety_wit_2 : delta_safety_wit_2.
Axiom proof_of_delta_return_wit_1 : delta_return_wit_1.
Axiom proof_of_delta_return_wit_2 : delta_return_wit_2.

End VC_Correct.
