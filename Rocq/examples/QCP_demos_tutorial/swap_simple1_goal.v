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

(*----- Function swap_int_pair -----*)

Definition swap_int_pair_entail_wit_1 := 
(
forall (p_pre: Z) (y: Z) (x: Z) ,
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
) \/
(
forall (p_pre: Z) (y: Z) (x: Z) ,
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
).

Definition swap_int_pair_entail_wit_1_split_goal_spatial := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
.

Definition swap_int_pair_return_wit_1 := 
(
forall (p_pre: Z) (y: Z) (x: Z) ,
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
|--
  (store_int_pair p_pre y x )
) \/
(
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (y <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (y >= INT_MIN)) ,
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
|--
  (store_int_pair p_pre y x )
).

Definition swap_int_pair_return_wit_1_split_goal_spatial := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (y <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (y >= INT_MIN)) ,
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
|--
  (store_int_pair p_pre y x )
.

Module Type VC_Correct.


Axiom proof_of_swap_int_pair_entail_wit_1 : swap_int_pair_entail_wit_1.
Axiom proof_of_swap_int_pair_return_wit_1 : swap_int_pair_return_wit_1.

End VC_Correct.
