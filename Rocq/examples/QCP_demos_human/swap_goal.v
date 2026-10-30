From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function swap -----*)

Definition swap_return_wit_1_eq :=
forall (x_eq: Z) (px_pre: Z) (py_pre: Z) (PreH1 : (px_pre = py_pre)),
  ((py_pre) # Int  |-> x_eq)
|--
  ((px_pre) # Int  |-> x_eq)
.

Definition swap_return_wit_2_neq :=
forall (y_neq: Z) (x_neq: Z) (px_pre: Z) (py_pre: Z),
  ((px_pre) # Int  |-> y_neq)
  **  ((py_pre) # Int  |-> x_neq)
|--
  ((px_pre) # Int  |-> y_neq)
  **  ((py_pre) # Int  |-> x_neq)
.

Definition swap_partial_solve_wit_1_eq :=
forall (x_eq: Z) (px_pre: Z) (py_pre: Z) (PreH1 : (px_pre = py_pre)),
  ((px_pre) # Int  |-> x_eq)
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int  |-> x_eq)
.

Definition swap_partial_solve_wit_2_eq :=
forall (x_eq: Z) (px_pre: Z) (py_pre: Z) (PreH1 : (px_pre = py_pre)),
  ((py_pre) # Int  |-> x_eq)
|--
  “ (px_pre = py_pre) ”
  &&  ((px_pre) # Int  |->_)
.

Definition swap_partial_solve_wit_3_eq :=
forall (x_eq: Z) (px_pre: Z) (py_pre: Z) (PreH1 : (px_pre = py_pre)),
  ((px_pre) # Int  |-> x_eq)
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int  |->_)
.

(*----- Function swap_test1 -----*)

Definition swap_test1_return_wit_1 :=
forall (x_pre: Z) (y_pre: Z) (x_v_2: Z) (y_v_2: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_v_2 = 1)) (PreH3 : (y_v_2 = 2)),
  ((x_pre) # Int  |-> y_v_2)
  **  ((y_pre) # Int  |-> x_v_2)
|--
  EX (x_v: Z) (y_v: Z),
  “ (y_v = 1) ”
  &&  “ (x_v = 2) ”
  &&  ((y_pre) # Int  |-> y_v)
  **  ((x_pre) # Int  |-> x_v)
.

Definition swap_test1_partial_solve_wit_1 :=
forall (x_pre: Z) (y_pre: Z) (x_v: Z) (y_v: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_v = 1)) (PreH3 : (y_v = 2)),
  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v)
|--
  “ (x_pre <> y_pre) ”
  &&  “ (x_v = 1) ”
  &&  “ (y_v = 2) ”
  &&  ((x_pre) # Int  |-> x_v)
  **  ((y_pre) # Int  |-> y_v)
.

(*----- Function swap_test2 -----*)

Definition swap_test2_return_wit_1 :=
forall (x_pre: Z) (y_pre: Z) (x_v: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_v = 1)),
  ((x_pre) # Int  |-> x_v)
|--
  EX (y_v: Z),
  “ (y_v = 1) ”
  &&  ((y_pre) # Int  |-> y_v)
.

Definition swap_test2_partial_solve_wit_1_pure :=
forall (x_pre: Z) (y_pre: Z) (x_v: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_v = 1)),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> x_v)
|--
  “ (x_pre = y_pre) ”
.

Definition swap_test2_partial_solve_wit_1_aux :=
forall (x_pre: Z) (y_pre: Z) (x_v: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_v = 1)),
  ((x_pre) # Int  |-> x_v)
|--
  “ (x_pre = y_pre) ”
  &&  “ (x_pre = y_pre) ”
  &&  “ (x_v = 1) ”
  &&  ((x_pre) # Int  |-> x_v)
.

Definition swap_test2_partial_solve_wit_1 := swap_test2_partial_solve_wit_1_pure -> swap_test2_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_swap_return_wit_1_eq : swap_return_wit_1_eq.
Axiom proof_of_swap_return_wit_2_neq : swap_return_wit_2_neq.
Axiom proof_of_swap_partial_solve_wit_1_eq : swap_partial_solve_wit_1_eq.
Axiom proof_of_swap_partial_solve_wit_2_eq : swap_partial_solve_wit_2_eq.
Axiom proof_of_swap_partial_solve_wit_3_eq : swap_partial_solve_wit_3_eq.
Axiom proof_of_swap_test1_return_wit_1 : swap_test1_return_wit_1.
Axiom proof_of_swap_test1_partial_solve_wit_1 : swap_test1_partial_solve_wit_1.
Axiom proof_of_swap_test2_return_wit_1 : swap_test2_return_wit_1.
Axiom proof_of_swap_test2_partial_solve_wit_1_pure : swap_test2_partial_solve_wit_1_pure.
Axiom proof_of_swap_test2_partial_solve_wit_1 : swap_test2_partial_solve_wit_1.

End VC_Correct.
