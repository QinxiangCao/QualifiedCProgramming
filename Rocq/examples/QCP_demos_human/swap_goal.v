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
Local Open Scope sac.

(*----- Function swap -----*)

Definition swap_return_wit_1_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) (PreH1 : (px_pre = py_pre)) ,
  ((py_pre) # Int  |-> x_eq)
|--
  ((px_pre) # Int  |-> x_eq)
.

Definition swap_return_wit_2_neq := 
forall (py_pre: Z) (px_pre: Z) (y_neq: Z) (x_neq: Z) ,
  ((px_pre) # Int  |-> y_neq)
  **  ((py_pre) # Int  |-> x_neq)
|--
  ((px_pre) # Int  |-> y_neq)
  **  ((py_pre) # Int  |-> x_neq)
.

Definition swap_partial_solve_wit_1_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) (PreH1 : (px_pre = py_pre)) ,
  ((px_pre) # Int  |-> x_eq)
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int  |-> x_eq)
.

Definition swap_partial_solve_wit_2_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) (PreH1 : (px_pre = py_pre)) ,
  ((py_pre) # Int  |-> x_eq)
|--
  “ (px_pre = py_pre) ”
  &&  ((px_pre) # Int  |->_)
.

Definition swap_partial_solve_wit_3_eq := 
forall (py_pre: Z) (px_pre: Z) (x_eq: Z) (PreH1 : (px_pre = py_pre)) ,
  ((px_pre) # Int  |-> x_eq)
|--
  “ (px_pre = py_pre) ”
  &&  ((py_pre) # Int  |->_)
.

(*----- Function swap_test1 -----*)

Definition swap_test1_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v_2: Z) (y_pre_v_2: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_pre_v_2 = 1)) (PreH3 : (y_pre_v_2 = 2)) ,
  ((x_pre) # Int  |-> y_pre_v_2)
  **  ((y_pre) # Int  |-> x_pre_v_2)
|--
  EX (x_pre_v: Z)  (y_pre_v: Z) ,
  “ (y_pre_v = 1) ” 
  &&  “ (x_pre_v = 2) ”
  &&  ((y_pre) # Int  |-> y_pre_v)
  **  ((x_pre) # Int  |-> x_pre_v)
.

Definition swap_test1_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) (y_pre_v: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_pre_v = 1)) (PreH3 : (y_pre_v = 2)) ,
  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)
|--
  “ (x_pre <> y_pre) ” 
  &&  “ (x_pre_v = 1) ” 
  &&  “ (y_pre_v = 2) ”
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)
.

(*----- Function swap_test2 -----*)

Definition swap_test2_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre_v = 1)) ,
  ((x_pre) # Int  |-> x_pre_v)
|--
  EX (y_pre_v: Z) ,
  “ (y_pre_v = 1) ”
  &&  ((y_pre) # Int  |-> y_pre_v)
.

Definition swap_test2_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre_v = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> x_pre_v)
|--
  “ (x_pre = y_pre) ”
.

Definition swap_test2_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (x_pre_v: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre_v = 1)) ,
  ((x_pre) # Int  |-> x_pre_v)
|--
  “ (x_pre = y_pre) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (x_pre_v = 1) ”
  &&  ((x_pre) # Int  |-> x_pre_v)
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
