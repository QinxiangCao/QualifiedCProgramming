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
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple4_strategy_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple4_strategy_proof.

(*----- Function swap_int_pair -----*)

Definition swap_int_pair_entail_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
.

Definition swap_int_pair_entail_wit_2 := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  ((( &( "temp" ) )) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  (store_int_pair p_pre y x )
  **  ((( &( "temp" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
.

Definition swap_int_pair_return_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  (store_int_pair p_pre y x )
|--
  (store_int_pair p_pre y x )
.

Module Type VC_Correct.

Include swap_simple4_Strategy_Correct.

Axiom proof_of_swap_int_pair_entail_wit_1 : swap_int_pair_entail_wit_1.
Axiom proof_of_swap_int_pair_entail_wit_2 : swap_int_pair_entail_wit_2.
Axiom proof_of_swap_int_pair_return_wit_1 : swap_int_pair_return_wit_1.

End VC_Correct.
