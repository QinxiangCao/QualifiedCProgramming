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
From SimpleC.EE.QCP_demos_LLM Require Import array3_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array3_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function touch_graph_one_read -----*)

Definition touch_graph_one_read_safety_wit_1 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : ((Zlength (cubes)) = 2)) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_graph_one_read_safety_wit_2 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : ((Zlength (cubes)) = 2)) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_graph_one_read_safety_wit_3 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : ((Zlength (cubes)) = 2)) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_graph_one_read_return_wit_1 := 
(
forall (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List_Z  __default__List__List_Z (PreH1 : ((Zlength (cubes)) = 2)) ,
  (IntArray.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))) 4 (replace_Znth (0) ((Znth (0) ((Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z)) (0))) ((Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z))) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) 0 0 3 4 (Znth 0 cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") 0 0 2 3 4 cubes )
|--
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
) \/
(
forall (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List_Z  __default__List__List_Z (PreH1 : ((Zlength (cubes)) = 2)) ,
  (IntArray.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))) 4 (replace_Znth (0) ((Znth (0) ((Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z)) (0))) ((Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z))) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) 0 0 3 4 (Znth 0 cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") 0 0 2 3 4 cubes )
|--
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
).

Definition touch_graph_one_read_return_wit_1_split_goal_spatial := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List_Z  __default__List__List_Z (PreH1 : ((Zlength (cubes)) = 2)) ,
  (IntArray.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))) 4 (replace_Znth (0) ((Znth (0) ((Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z)) (0))) ((Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z))) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) 0 0 3 4 (Znth 0 cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") 0 0 2 3 4 cubes )
|--
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_one_read_partial_solve_wit_1 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List_Z  __default__List__List_Z (PreH1 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ ((Zlength (cubes)) = 2) ”
  &&  (((((&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))) + (0 * sizeof(INT)))) # Int  |-> (Znth (0) ((Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z)) (0)))
  **  (IntArray.missing_i ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))) 0 0 4 (Znth 0 (Znth 0 cubes __default__List__List_Z) __default__List_Z) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (0 * ((sizeof(INT) * 4) * 3))) 0 0 3 4 (Znth 0 cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") 0 0 2 3 4 cubes )
.

Module Type VC_Correct.

Include array3_Strategy_Correct.
Include array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_touch_graph_one_read_safety_wit_1 : touch_graph_one_read_safety_wit_1.
Axiom proof_of_touch_graph_one_read_safety_wit_2 : touch_graph_one_read_safety_wit_2.
Axiom proof_of_touch_graph_one_read_safety_wit_3 : touch_graph_one_read_safety_wit_3.
Axiom proof_of_touch_graph_one_read_return_wit_1 : touch_graph_one_read_return_wit_1.
Axiom proof_of_touch_graph_one_read_partial_solve_wit_1 : touch_graph_one_read_partial_solve_wit_1.

End VC_Correct.
