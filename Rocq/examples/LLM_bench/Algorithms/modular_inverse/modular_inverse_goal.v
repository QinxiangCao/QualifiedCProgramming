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
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib.
Local Open Scope sac.

(*----- Function modular_inverse -----*)

Definition modular_inverse_safety_wit_1 := 
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH2 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (1 < modulus_pre)) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre < modulus_pre)) (PreH6 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_callee_v)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ ((x_callee_v <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_inverse_safety_wit_2 := 
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH2 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (1 < modulus_pre)) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre < modulus_pre)) (PreH6 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int  |-> (x_callee_v % ( modulus_pre ) ))
  **  ((( &( "x" ) )) # Int  |-> x_callee_v)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition modular_inverse_safety_wit_3 := 
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) < 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "inverse" ) )) # Int  |-> (x_callee_v % ( modulus_pre ) ))
  **  ((( &( "x" ) )) # Int  |-> x_callee_v)
  **  ((( &( "y" ) )) # Int  |-> y_callee_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (((x_callee_v % ( modulus_pre ) ) + modulus_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x_callee_v % ( modulus_pre ) ) + modulus_pre )) ”
.

Definition modular_inverse_return_wit_1 := 
(
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) < 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (0 <= ((x_callee_v % ( modulus_pre ) ) + modulus_pre )) ” 
  &&  “ (((x_callee_v % ( modulus_pre ) ) + modulus_pre ) < modulus_pre) ” 
  &&  “ (ModularInverse a_pre modulus_pre ((x_callee_v % ( modulus_pre ) ) + modulus_pre ) ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) < 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (ModularInverse a_pre modulus_pre ((x_callee_v % ( modulus_pre ) ) + modulus_pre ) ) ” 
  &&  “ (0 <= ((x_callee_v % ( modulus_pre ) ) + modulus_pre )) ”
  &&  emp
).

Definition modular_inverse_return_wit_1_split_goal_1 := 
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) < 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  (ModularInverse a_pre modulus_pre ((x_callee_v % ( modulus_pre ) ) + modulus_pre ) )
.

Definition modular_inverse_return_wit_1_split_goal_2 := 
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) < 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  (0 <= ((x_callee_v % ( modulus_pre ) ) + modulus_pre ))
.

Definition modular_inverse_return_wit_2 := 
(
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) >= 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (0 <= (x_callee_v % ( modulus_pre ) )) ” 
  &&  “ ((x_callee_v % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (ModularInverse a_pre modulus_pre (x_callee_v % ( modulus_pre ) ) ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) >= 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (ModularInverse a_pre modulus_pre (x_callee_v % ( modulus_pre ) ) ) ” 
  &&  “ ((x_callee_v % ( modulus_pre ) ) < modulus_pre) ”
  &&  emp
).

Definition modular_inverse_return_wit_2_split_goal_1 := 
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) >= 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  (ModularInverse a_pre modulus_pre (x_callee_v % ( modulus_pre ) ) )
.

Definition modular_inverse_return_wit_2_split_goal_2 := 
forall (modulus_pre: Z) (a_pre: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((x_callee_v % ( modulus_pre ) ) >= 0)) (PreH2 : (retval = (Zgcd (a_pre) (modulus_pre)))) (PreH3 : (((a_pre * x_callee_v ) + (modulus_pre * y_callee_v ) ) = (Zgcd (a_pre) (modulus_pre)))) (PreH4 : (1 < modulus_pre)) (PreH5 : (0 < a_pre)) (PreH6 : (a_pre < modulus_pre)) (PreH7 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((x_callee_v % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_inverse_partial_solve_wit_1_pure := 
forall (modulus_pre: Z) (a_pre: Z) (PreH1 : (1 < modulus_pre)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (INT_MIN < modulus_pre) ” 
  &&  “ (modulus_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ”
.

Definition modular_inverse_partial_solve_wit_1_aux := 
forall (modulus_pre: Z) (a_pre: Z) (PreH1 : (1 < modulus_pre)) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : ((Zgcd (a_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (INT_MIN < modulus_pre) ” 
  &&  “ (modulus_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (1 < modulus_pre) ” 
  &&  “ (0 < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ ((Zgcd (a_pre) (modulus_pre)) = 1) ”
  &&  emp
.

Definition modular_inverse_partial_solve_wit_1 := modular_inverse_partial_solve_wit_1_pure -> modular_inverse_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_modular_inverse_safety_wit_1 : modular_inverse_safety_wit_1.
Axiom proof_of_modular_inverse_safety_wit_2 : modular_inverse_safety_wit_2.
Axiom proof_of_modular_inverse_safety_wit_3 : modular_inverse_safety_wit_3.
Axiom proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1.
Axiom proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2.
Axiom proof_of_modular_inverse_partial_solve_wit_1_pure : modular_inverse_partial_solve_wit_1_pure.
Axiom proof_of_modular_inverse_partial_solve_wit_1 : modular_inverse_partial_solve_wit_1.

End VC_Correct.
