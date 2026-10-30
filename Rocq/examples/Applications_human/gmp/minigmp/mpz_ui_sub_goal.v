From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_ui_sub -----*)

Definition mpz_ui_sub_return_wit_1 :=
(
forall (a0_r_eq_b: Z) (zb_r_eq_b: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = b_pre)) (PreH2 : (r_pre = b_pre)) (PreH3 : (a_pre = a0_r_eq_b)) (PreH4 : (0 <= a0_r_eq_b)),
  (store_Z r_pre ((-zb_r_eq_b) + a0_r_eq_b ) )
|--
  (store_Z b_pre (a0_r_eq_b - zb_r_eq_b ) )
) \/
(
forall (a0_r_eq_b: Z) (zb_r_eq_b: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = b_pre)) (PreH2 : (r_pre = b_pre)) (PreH3 : (a_pre = a0_r_eq_b)) (PreH4 : (0 <= a0_r_eq_b)),
  (store_Z r_pre ((-zb_r_eq_b) + a0_r_eq_b ) )
|--
  (store_Z b_pre (a0_r_eq_b - zb_r_eq_b ) )
).

Definition mpz_ui_sub_return_wit_1_split_goal_spatial :=
forall (a0_r_eq_b: Z) (zb_r_eq_b: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = b_pre)) (PreH2 : (r_pre = b_pre)) (PreH3 : (a_pre = a0_r_eq_b)) (PreH4 : (0 <= a0_r_eq_b)),
  (store_Z r_pre ((-zb_r_eq_b) + a0_r_eq_b ) )
|--
  (store_Z b_pre (a0_r_eq_b - zb_r_eq_b ) )
.

Definition mpz_ui_sub_partial_solve_wit_1_pure :=
forall (a0_r_eq_b: Z) (zb_r_eq_b: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = b_pre)) (PreH2 : (a_pre = a0_r_eq_b)) (PreH3 : (0 <= a0_r_eq_b)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # UInt  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z b_pre zb_r_eq_b )
|--
  “ (r_pre = b_pre) ”
.

Definition mpz_ui_sub_partial_solve_wit_1_aux :=
forall (a0_r_eq_b: Z) (zb_r_eq_b: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = b_pre)) (PreH2 : (a_pre = a0_r_eq_b)) (PreH3 : (0 <= a0_r_eq_b)),
  (store_Z b_pre zb_r_eq_b )
|--
  “ (r_pre = b_pre) ”
  &&  “ (r_pre = b_pre) ”
  &&  “ (a_pre = a0_r_eq_b) ”
  &&  “ (0 <= a0_r_eq_b) ”
  &&  (store_Z b_pre zb_r_eq_b )
.

Definition mpz_ui_sub_partial_solve_wit_1 := mpz_ui_sub_partial_solve_wit_1_pure -> mpz_ui_sub_partial_solve_wit_1_aux.

Definition mpz_ui_sub_partial_solve_wit_2_pure :=
forall (a0_r_eq_b: Z) (zb_r_eq_b: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = b_pre)) (PreH2 : (r_pre = b_pre)) (PreH3 : (a_pre = a0_r_eq_b)) (PreH4 : (0 <= a0_r_eq_b)),
  (store_Z b_pre (-zb_r_eq_b) )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # UInt  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (r_pre = r_pre) ”
  &&  “ (a_pre = a0_r_eq_b) ”
  &&  “ (0 <= a0_r_eq_b) ”
.

Definition mpz_ui_sub_partial_solve_wit_2_aux :=
forall (a0_r_eq_b: Z) (zb_r_eq_b: Z) (r_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (r_pre = b_pre)) (PreH2 : (r_pre = b_pre)) (PreH3 : (a_pre = a0_r_eq_b)) (PreH4 : (0 <= a0_r_eq_b)),
  (store_Z b_pre (-zb_r_eq_b) )
|--
  “ (r_pre = r_pre) ”
  &&  “ (a_pre = a0_r_eq_b) ”
  &&  “ (0 <= a0_r_eq_b) ”
  &&  “ (r_pre = b_pre) ”
  &&  “ (r_pre = b_pre) ”
  &&  “ (a_pre = a0_r_eq_b) ”
  &&  “ (0 <= a0_r_eq_b) ”
  &&  (store_Z r_pre (-zb_r_eq_b) )
.

Definition mpz_ui_sub_partial_solve_wit_2 := mpz_ui_sub_partial_solve_wit_2_pure -> mpz_ui_sub_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_ui_sub_return_wit_1 : mpz_ui_sub_return_wit_1.
Axiom proof_of_mpz_ui_sub_partial_solve_wit_1_pure : mpz_ui_sub_partial_solve_wit_1_pure.
Axiom proof_of_mpz_ui_sub_partial_solve_wit_1 : mpz_ui_sub_partial_solve_wit_1.
Axiom proof_of_mpz_ui_sub_partial_solve_wit_2_pure : mpz_ui_sub_partial_solve_wit_2_pure.
Axiom proof_of_mpz_ui_sub_partial_solve_wit_2 : mpz_ui_sub_partial_solve_wit_2.

End VC_Correct.
