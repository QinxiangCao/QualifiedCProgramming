From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function max3 -----*)

Definition max3_return_wit_1 :=
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (PreH1 : (x_pre >= z_pre)) (PreH2 : (x_pre >= y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)),
  TT && emp 
|--
  “ (x_pre >= x_pre) ”
  &&  “ (x_pre >= y_pre) ”
  &&  “ (x_pre >= z_pre) ”
  &&  emp
.

Definition max3_return_wit_2 :=
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (PreH1 : (x_pre < z_pre)) (PreH2 : (x_pre >= y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)),
  TT && emp 
|--
  “ (z_pre >= x_pre) ”
  &&  “ (z_pre >= y_pre) ”
  &&  “ (z_pre >= z_pre) ”
  &&  emp
.

Definition max3_return_wit_3 :=
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (PreH1 : (y_pre >= z_pre)) (PreH2 : (x_pre < y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)),
  TT && emp 
|--
  “ (y_pre >= x_pre) ”
  &&  “ (y_pre >= y_pre) ”
  &&  “ (y_pre >= z_pre) ”
  &&  emp
.

Definition max3_return_wit_4 :=
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (PreH1 : (y_pre < z_pre)) (PreH2 : (x_pre < y_pre)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (INT_MIN <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (INT_MIN <= z_pre)) (PreH8 : (z_pre <= INT_MAX)),
  TT && emp 
|--
  “ (z_pre >= x_pre) ”
  &&  “ (z_pre >= y_pre) ”
  &&  “ (z_pre >= z_pre) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_max3_return_wit_1 : max3_return_wit_1.
Axiom proof_of_max3_return_wit_2 : max3_return_wit_2.
Axiom proof_of_max3_return_wit_3 : max3_return_wit_3.
Axiom proof_of_max3_return_wit_4 : max3_return_wit_4.

End VC_Correct.
