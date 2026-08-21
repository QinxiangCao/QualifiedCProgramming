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
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Require Import Algorithms.DFS.DFS.
Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_matrix_lib.
Import ZSimpleGraph.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import graph_matrix_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import graph_matrix_strategy_proof.

(*----- Function dfs_adjacency_matrix -----*)

Definition dfs_adjacency_matrix_safety_wit_1 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs_adjacency_matrix_safety_wit_2 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  ((( &( "neighbor" ) )) # Int  |->_)
  **  (IntArray.full visited_pre vertex_count_pre (replace_Znth (vertex_pre) (1) (values)) )
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_matrix_safety_wit_3 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ (((vertex_pre * vertex_count_pre ) + neighbor ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((vertex_pre * vertex_count_pre ) + neighbor )) ”
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ (((vertex_pre * vertex_count_pre ) + neighbor ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((vertex_pre * vertex_count_pre ) + neighbor )) ”
).

Definition dfs_adjacency_matrix_safety_wit_3_split_goal_1 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ (((vertex_pre * vertex_count_pre ) + neighbor ) <= INT_MAX) ”
.

Definition dfs_adjacency_matrix_safety_wit_3_split_goal_2 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ ((INT_MIN) <= ((vertex_pre * vertex_count_pre ) + neighbor )) ”
.

Definition dfs_adjacency_matrix_safety_wit_4 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ ((vertex_pre * vertex_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (vertex_pre * vertex_count_pre )) ”
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ ((vertex_pre * vertex_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (vertex_pre * vertex_count_pre )) ”
).

Definition dfs_adjacency_matrix_safety_wit_4_split_goal_1 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ ((vertex_pre * vertex_count_pre ) <= INT_MAX) ”
.

Definition dfs_adjacency_matrix_safety_wit_4_split_goal_2 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ ((INT_MIN) <= (vertex_pre * vertex_count_pre )) ”
.

Definition dfs_adjacency_matrix_safety_wit_5 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH2 : (neighbor < vertex_count_pre)) (PreH3 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH4 : (0 < vertex_count_pre)) (PreH5 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (0 <= neighbor)) (PreH10 : (neighbor <= vertex_count_pre)) (PreH11 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH12 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH13 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH14 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_matrix_safety_wit_6 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <> 0)) (PreH2 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH3 : (neighbor < vertex_count_pre)) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (0 <= neighbor)) (PreH11 : (neighbor <= vertex_count_pre)) (PreH12 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH13 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH14 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntArray.full visited_pre vertex_count_pre values1 )
  **  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_matrix_safety_wit_7 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (visited_set2: (Z -> Prop)) (values2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 )) (PreH10 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 )) (PreH11 : (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH12 : (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
|--
  “ ((neighbor + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (neighbor + 1 )) ”
.

Definition dfs_adjacency_matrix_entail_wit_1 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec visited_set_low_level_spec )
|--
  EX (values: (@list Z)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec visited_set_low_level_spec )
|--
  EX (values: (@list Z)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
).

Definition dfs_adjacency_matrix_entail_wit_2 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  (IntArray.full visited_pre vertex_count_pre (replace_Znth (vertex_pre) (1) (values)) )
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
|--
  EX (values1: (@list Z))  (visited_set1: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre 0 visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  TT && emp 
|--
  EX (visited_set1: (Z -> Prop)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre 0 visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec (replace_Znth (vertex_pre) (1) (values)) visited_set1 ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_entail_wit_3 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth neighbor values1 0) = 0)) (PreH2 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <> 0)) (PreH3 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH4 : (neighbor < vertex_count_pre)) (PreH5 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH6 : (0 < vertex_count_pre)) (PreH7 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH8 : (0 <= vertex_pre)) (PreH9 : (vertex_pre < vertex_count_pre)) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH11 : (0 <= neighbor)) (PreH12 : (neighbor <= vertex_count_pre)) (PreH13 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH14 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH15 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH16 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntArray.full visited_pre vertex_count_pre values1 )
  **  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
|--
  EX (call_visited_set: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor ) ” 
  &&  “ ~((call_visited_set neighbor )) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec call_visited_set ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec call_visited_set )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth neighbor values1 0) = 0)) (PreH4 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <> 0)) (PreH5 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH6 : (neighbor < vertex_count_pre)) (PreH7 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH8 : (0 < vertex_count_pre)) (PreH9 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH10 : (0 <= vertex_pre)) (PreH11 : (vertex_pre < vertex_count_pre)) (PreH12 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH13 : (0 <= neighbor)) (PreH14 : (neighbor <= vertex_count_pre)) (PreH15 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH16 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH17 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH18 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntArray.full visited_pre vertex_count_pre values1 )
  **  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
|--
  EX (call_visited_set: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor ) ” 
  &&  “ ~((call_visited_set neighbor )) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec call_visited_set ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec call_visited_set )
).

Definition dfs_adjacency_matrix_entail_wit_4_1 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (call_visited_set: (Z -> Prop)) (bind_visited_set: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix.visited_extension call_visited_set bind_visited_set )) (PreH2 : (bind_visited_set neighbor )) (PreH3 : (safeExec (eq (bind_visited_set)) (applyf ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre))) (tt)) X_low_level_spec )) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (0 <= neighbor)) (PreH10 : (neighbor < vertex_count_pre)) (PreH11 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH12 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH13 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH14 : ~((call_visited_set neighbor ))) (PreH15 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH16 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec call_visited_set )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec bind_visited_set )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (call_visited_set: (Z -> Prop)) (bind_visited_set: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix.visited_extension call_visited_set bind_visited_set )) (PreH2 : (bind_visited_set neighbor )) (PreH3 : (safeExec (eq (bind_visited_set)) (applyf ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre))) (tt)) X_low_level_spec )) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (0 <= neighbor)) (PreH10 : (neighbor < vertex_count_pre)) (PreH11 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH12 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH13 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH14 : ~((call_visited_set neighbor ))) (PreH15 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH16 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec call_visited_set )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec bind_visited_set )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
).

Definition dfs_adjacency_matrix_entail_wit_4_2 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) = 0)) (PreH2 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH3 : (neighbor < vertex_count_pre)) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (0 <= neighbor)) (PreH11 : (neighbor <= vertex_count_pre)) (PreH12 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH13 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH14 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) = 0)) (PreH4 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH5 : (neighbor < vertex_count_pre)) (PreH6 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH7 : (0 < vertex_count_pre)) (PreH8 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH9 : (0 <= vertex_pre)) (PreH10 : (vertex_pre < vertex_count_pre)) (PreH11 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH12 : (0 <= neighbor)) (PreH13 : (neighbor <= vertex_count_pre)) (PreH14 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH15 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH16 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH17 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
|--
  EX (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set2 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
).

Definition dfs_adjacency_matrix_entail_wit_4_3 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth neighbor values1 0) <> 0)) (PreH2 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <> 0)) (PreH3 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH4 : (neighbor < vertex_count_pre)) (PreH5 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH6 : (0 < vertex_count_pre)) (PreH7 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH8 : (0 <= vertex_pre)) (PreH9 : (vertex_pre < vertex_count_pre)) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH11 : (0 <= neighbor)) (PreH12 : (neighbor <= vertex_count_pre)) (PreH13 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH14 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH15 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH16 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntArray.full visited_pre vertex_count_pre values1 )
  **  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth neighbor values1 0) <> 0)) (PreH4 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <> 0)) (PreH5 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH6 : (neighbor < vertex_count_pre)) (PreH7 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH8 : (0 < vertex_count_pre)) (PreH9 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH10 : (0 <= vertex_pre)) (PreH11 : (vertex_pre < vertex_count_pre)) (PreH12 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH13 : (0 <= neighbor)) (PreH14 : (neighbor <= vertex_count_pre)) (PreH15 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH16 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH17 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH18 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
|--
  EX (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set2 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
).

Definition dfs_adjacency_matrix_entail_wit_5 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (visited_set2: (Z -> Prop)) (values2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 )) (PreH10 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 )) (PreH11 : (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH12 : (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
|--
  EX (values1: (@list Z))  (visited_set1: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (0 <= (neighbor + 1 )) ” 
  &&  “ ((neighbor + 1 ) <= vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (g_low_level_spec: G) (neighbor: Z) (visited_set2: (Z -> Prop)) (values2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 )) (PreH10 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set2 )) (PreH11 : (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH12 : (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 )) ,
  TT && emp 
|--
  EX (visited_set1: (Z -> Prop)) ,
  “ (0 <= (neighbor + 1 )) ” 
  &&  “ ((neighbor + 1 ) <= (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set1 ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_entail_wit_6 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor >= vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  EX (visited_set_out: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set_out ) ” 
  &&  “ (visited_set_out vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec visited_set_out )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor >= vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  EX (visited_set_out: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set_out ) ” 
  &&  “ (visited_set_out vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec visited_set_out )
).

Definition dfs_adjacency_matrix_return_wit_1 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (visited_set_out: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set_out )) (PreH2 : (visited_set_out vertex_pre )) (PreH3 : (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec visited_set_out )
|--
  EX (low_visited_set: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec low_visited_set ) ” 
  &&  “ (low_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec low_visited_set )
) \/
(
forall (vertex_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (visited_set_out: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set_out )) (PreH2 : (visited_set_out vertex_pre )) (PreH3 : (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (low_visited_set: (Z -> Prop)) ,
  “ (low_visited_set vertex_pre ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_partial_solve_wit_1 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (((visited_pre + (vertex_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i visited_pre vertex_pre 0 vertex_count_pre values )
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
.

Definition dfs_adjacency_matrix_partial_solve_wit_2 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor <= vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 ) ”
  &&  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
.

Definition dfs_adjacency_matrix_partial_solve_wit_3 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z)  __default__List_Z (PreH1 : ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <> 0)) (PreH2 : (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH3 : (neighbor < vertex_count_pre)) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (0 <= neighbor)) (PreH11 : (neighbor <= vertex_count_pre)) (PreH12 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH13 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 )) (PreH14 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  “ ((Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)) <> 0) ” 
  &&  “ (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor <= vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 ) ”
  &&  (((visited_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth neighbor values1 0))
  **  (IntArray.missing_i visited_pre neighbor 0 vertex_count_pre values1 )
  **  (((matrix_pre + (((vertex_pre * vertex_count_pre ) + neighbor ) * sizeof(INT)))) # Int  |-> (Znth (neighbor) ((Znth vertex_pre rows_low_level_spec __default__List_Z)) (0)))
  **  (IntArray.missing_i (matrix_pre + ((vertex_pre * vertex_count_pre ) * sizeof(INT))) neighbor 0 vertex_count_pre (Znth vertex_pre rows_low_level_spec __default__List_Z) )
  **  (IntArray2.missing_i matrix_pre vertex_pre 0 vertex_count_pre vertex_count_pre rows_low_level_spec )
.

Definition dfs_adjacency_matrix_partial_solve_wit_4_pure := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (call_visited_set: (Z -> Prop)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH10 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH11 : ~((call_visited_set neighbor ))) (PreH12 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH13 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec call_visited_set )) (PreH14 : (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec call_visited_set )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
.

Definition dfs_adjacency_matrix_partial_solve_wit_4_aux := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (call_visited_set: (Z -> Prop)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : ((vertex_count_pre * vertex_count_pre ) < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH10 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH11 : ~((call_visited_set neighbor ))) (PreH12 : (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH13 : (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec call_visited_set )) (PreH14 : (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec )) ,
  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec call_visited_set )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ” 
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor ) ” 
  &&  “ ~((call_visited_set neighbor )) ” 
  &&  “ (DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec call_visited_set ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec call_visited_set )
.

Definition dfs_adjacency_matrix_partial_solve_wit_4 := dfs_adjacency_matrix_partial_solve_wit_4_pure -> dfs_adjacency_matrix_partial_solve_wit_4_aux.

Definition dfs_adjacency_matrix_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_bind_spec: (B -> ((Z -> Prop) -> Prop))) (c_bind_spec: (unit -> (@ StateRelMonad.M  (Z -> Prop) B))) (visited_set_bind_spec: (Z -> Prop)) (rows_bind_spec: (@list (@list Z))) (g_bind_spec: G) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_bind_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_bind_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_bind_spec)) (bind ((DFSAdjacencyMatrix.dfs_program (g_bind_spec) (vertex_pre))) (c_bind_spec)) X_bind_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_bind_spec)) matrix_pre rows_bind_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_bind_spec visited_set_bind_spec )
|--
EX (g_low_level_spec: G) (rows_low_level_spec: (@list (@list Z))) (visited_set_low_level_spec: (Z -> Prop)) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) ,
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec visited_set_low_level_spec ))
  **
  ((EX low_visited_set,
  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec low_visited_set ) ” 
  &&  “ (low_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec low_visited_set ))
  -*
  (EX bind_visited_set,
  “ (DFSAdjacencyMatrix.visited_extension visited_set_bind_spec bind_visited_set ) ” 
  &&  “ (bind_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (bind_visited_set)) (applyf (c_bind_spec) (tt)) X_bind_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_bind_spec)) matrix_pre rows_bind_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_bind_spec bind_visited_set )))
.

Definition dfs_adjacency_matrix_derive_high_level_spec_by_low_level_spec := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (initial_visited_set_high_level_spec: (Z -> Prop)) (g_high_level_spec: G) ,
  EX rows,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_high_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_high_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix.empty_visited initial_visited_set_high_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_high_level_spec)) matrix_pre rows )
  **  (DFSAdjacencyMatrix.visited visited_pre g_high_level_spec initial_visited_set_high_level_spec )
|--
EX (g_low_level_spec: G) (rows_low_level_spec: (@list (@list Z))) (visited_set_low_level_spec: (Z -> Prop)) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) ,
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ ((vertex_count_pre * vertex_count_pre ) < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec visited_set_low_level_spec ))
  **
  ((EX low_visited_set,
  “ (DFSAdjacencyMatrix.visited_extension visited_set_low_level_spec low_visited_set ) ” 
  &&  “ (low_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_low_level_spec)) matrix_pre rows_low_level_spec )
  **  (DFSAdjacencyMatrix.visited visited_pre g_low_level_spec low_visited_set ))
  -*
  (EX rows_2 high_visited_set,
  “ forall (v: Z) , ((high_visited_set v ) -> (DFSAdjacencyMatrix.graph_reachable g_high_level_spec vertex_pre v )) ” 
  &&  “ forall (v_2: Z) , ((DFSAdjacencyMatrix.graph_reachable g_high_level_spec vertex_pre v_2 ) -> (high_visited_set v_2 )) ”
  &&  (GraphMatrixFlat.graph_rep vertex_count_pre (DFSAdjacencyMatrix.adjacency_matrix_model (g_high_level_spec)) matrix_pre rows_2 )
  **  (DFSAdjacencyMatrix.visited visited_pre g_high_level_spec high_visited_set )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include array2_Strategy_Correct.
Include int_array_Strategy_Correct.
Include int_ptr_array2_Strategy_Correct.
Include graph_matrix_Strategy_Correct.

Axiom proof_of_dfs_adjacency_matrix_safety_wit_1 : dfs_adjacency_matrix_safety_wit_1.
Axiom proof_of_dfs_adjacency_matrix_safety_wit_2 : dfs_adjacency_matrix_safety_wit_2.
Axiom proof_of_dfs_adjacency_matrix_safety_wit_3 : dfs_adjacency_matrix_safety_wit_3.
Axiom proof_of_dfs_adjacency_matrix_safety_wit_4 : dfs_adjacency_matrix_safety_wit_4.
Axiom proof_of_dfs_adjacency_matrix_safety_wit_5 : dfs_adjacency_matrix_safety_wit_5.
Axiom proof_of_dfs_adjacency_matrix_safety_wit_6 : dfs_adjacency_matrix_safety_wit_6.
Axiom proof_of_dfs_adjacency_matrix_safety_wit_7 : dfs_adjacency_matrix_safety_wit_7.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_1 : dfs_adjacency_matrix_entail_wit_1.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_2 : dfs_adjacency_matrix_entail_wit_2.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_3 : dfs_adjacency_matrix_entail_wit_3.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_4_1 : dfs_adjacency_matrix_entail_wit_4_1.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_4_2 : dfs_adjacency_matrix_entail_wit_4_2.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_4_3 : dfs_adjacency_matrix_entail_wit_4_3.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_5 : dfs_adjacency_matrix_entail_wit_5.
Axiom proof_of_dfs_adjacency_matrix_entail_wit_6 : dfs_adjacency_matrix_entail_wit_6.
Axiom proof_of_dfs_adjacency_matrix_return_wit_1 : dfs_adjacency_matrix_return_wit_1.
Axiom proof_of_dfs_adjacency_matrix_partial_solve_wit_1 : dfs_adjacency_matrix_partial_solve_wit_1.
Axiom proof_of_dfs_adjacency_matrix_partial_solve_wit_2 : dfs_adjacency_matrix_partial_solve_wit_2.
Axiom proof_of_dfs_adjacency_matrix_partial_solve_wit_3 : dfs_adjacency_matrix_partial_solve_wit_3.
Axiom proof_of_dfs_adjacency_matrix_partial_solve_wit_4_pure : dfs_adjacency_matrix_partial_solve_wit_4_pure.
Axiom proof_of_dfs_adjacency_matrix_partial_solve_wit_4 : dfs_adjacency_matrix_partial_solve_wit_4.
Axiom proof_of_dfs_adjacency_matrix_derive_bind_spec_by_low_level_spec : dfs_adjacency_matrix_derive_bind_spec_by_low_level_spec.
Axiom proof_of_dfs_adjacency_matrix_derive_high_level_spec_by_low_level_spec : dfs_adjacency_matrix_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
