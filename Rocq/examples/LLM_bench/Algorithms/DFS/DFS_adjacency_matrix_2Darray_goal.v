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
Require Import Algorithms.DFS.DFS.
Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_matrix_2Darray_lib.
Import ZSimpleGraph.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function dfs_adjacency_matrix_2Darray -----*)

Definition dfs_adjacency_matrix_2Darray_safety_wit_1 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH9 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH10 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs_adjacency_matrix_2Darray_safety_wit_2 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH9 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH10 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  ((( &( "neighbor" ) )) # Int  |->_)
  **  (IntArray.full visited_pre vertex_count_pre (replace_Znth (vertex_pre) (1) (values)) )
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_matrix_2Darray_safety_wit_3 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH12 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH15 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_exists" ) )) # Int  |-> edge_exists)
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre scan_values2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_matrix_2Darray_safety_wit_4 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : (edge_exists <> 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (0 <= neighbor)) (PreH8 : (neighbor < vertex_count_pre)) (PreH9 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH11 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH12 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH13 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH14 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH16 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntArray.full visited_pre vertex_count_pre scan_values2 )
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_exists" ) )) # Int  |-> edge_exists)
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_matrix_2Darray_safety_wit_5 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (edge_exists: Z) (visited_set2: (Z -> Prop)) (values2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 )) (PreH12 : (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
|--
  “ ((neighbor + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (neighbor + 1 )) ”
.

Definition dfs_adjacency_matrix_2Darray_entail_wit_1 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) ,
  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec visited_set_low_level_spec )
|--
  EX (values: (@list Z)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) ,
  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec visited_set_low_level_spec )
|--
  EX (values: (@list Z)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_2 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH9 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH10 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  (IntArray.full visited_pre vertex_count_pre (replace_Znth (vertex_pre) (1) (values)) )
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
|--
  EX (values1: (@list Z))  (visited_set1: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre 0 visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH9 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH10 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  TT && emp 
|--
  EX (visited_set1: (Z -> Prop)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre 0 visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec (replace_Znth (vertex_pre) (1) (values)) visited_set1 ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_3 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  EX (row_ptr: Z)  (scan_values: (@list Z))  (scan_visited_set: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set ) ” 
  &&  “ (safeExec (eq (scan_visited_set)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec scan_values scan_visited_set ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ”
  &&  (IntPtrArray2.missing_i matrix_pre vertex_count_pre vertex_pre row_ptr rows_low_level_spec )
  **  (((matrix_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited_pre vertex_count_pre scan_values )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (neighbor < vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth vertex_pre rows_low_level_spec __default__List_Z))) (Znth vertex_pre rows_low_level_spec __default__List_Z) )
|--
  EX (scan_visited_set: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set ) ” 
  &&  “ (safeExec (eq (scan_visited_set)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 scan_visited_set ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ”
  &&  (IntArray.full row_ptr_2 (Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) )
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_4 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set: (Z -> Prop)) (scan_values: (@list Z)) (row_ptr: Z) (neighbor: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set )) (PreH10 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set )) (PreH11 : (safeExec (eq (scan_visited_set)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH12 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec scan_values scan_visited_set )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntArray.full row_ptr (Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i matrix_pre vertex_count_pre vertex_pre row_ptr rows_low_level_spec )
  **  (((matrix_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited_pre vertex_count_pre scan_values )
|--
  EX (scan_values2: (@list Z))  (scan_visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ ((Znth neighbor (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) 0) = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 ) ” 
  &&  “ (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre scan_values2 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set: (Z -> Prop)) (scan_values: (@list Z)) (row_ptr: Z) (neighbor: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set )) (PreH10 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set )) (PreH11 : (safeExec (eq (scan_visited_set)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH12 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec scan_values scan_visited_set )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntArray.full row_ptr (Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i matrix_pre vertex_count_pre vertex_pre row_ptr rows_low_level_spec )
  **  (((matrix_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  EX (scan_visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ ((Znth neighbor (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) 0) = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 ) ” 
  &&  “ (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec scan_values scan_visited_set2 ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_5 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : ((Znth neighbor scan_values2 0) = 0)) (PreH2 : (edge_exists <> 0)) (PreH3 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH4 : (0 < vertex_count_pre)) (PreH5 : (vertex_count_pre < INT_MAX)) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH11 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH12 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH13 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH14 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH15 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH16 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH17 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntArray.full visited_pre vertex_count_pre scan_values2 )
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
|--
  EX (call_visited_set: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor ) ” 
  &&  “ ~((call_visited_set neighbor )) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec call_visited_set ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec call_visited_set )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : ((Znth neighbor scan_values2 0) = 0)) (PreH2 : (edge_exists <> 0)) (PreH3 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH4 : (0 < vertex_count_pre)) (PreH5 : (vertex_count_pre < INT_MAX)) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH11 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH12 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH13 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH14 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH15 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH16 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH17 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntArray.full visited_pre vertex_count_pre scan_values2 )
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
|--
  EX (call_visited_set: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor ) ” 
  &&  “ ~((call_visited_set neighbor )) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec call_visited_set ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec call_visited_set )
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_6_1 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (edge_exists: Z) (call_visited_set: (Z -> Prop)) (bind_visited_set: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix2Darray.visited_extension call_visited_set bind_visited_set )) (PreH2 : (bind_visited_set neighbor )) (PreH3 : (safeExec (eq (bind_visited_set)) (applyf ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre))) (tt)) X_low_level_spec )) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : (vertex_count_pre < INT_MAX)) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (0 <= neighbor)) (PreH10 : (neighbor < vertex_count_pre)) (PreH11 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH12 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH13 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH14 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH15 : ~((call_visited_set neighbor ))) (PreH16 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH17 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH18 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH19 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec call_visited_set )) ,
  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec bind_visited_set )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (edge_exists: Z) (call_visited_set: (Z -> Prop)) (bind_visited_set: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix2Darray.visited_extension call_visited_set bind_visited_set )) (PreH2 : (bind_visited_set neighbor )) (PreH3 : (safeExec (eq (bind_visited_set)) (applyf ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre))) (tt)) X_low_level_spec )) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : (vertex_count_pre < INT_MAX)) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (0 <= neighbor)) (PreH10 : (neighbor < vertex_count_pre)) (PreH11 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH12 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH13 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH14 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH15 : ~((call_visited_set neighbor ))) (PreH16 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH17 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH18 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH19 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec call_visited_set )) ,
  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec bind_visited_set )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_6_2 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : (edge_exists = 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (0 <= neighbor)) (PreH8 : (neighbor < vertex_count_pre)) (PreH9 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH11 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH12 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH13 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH14 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH16 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre scan_values2 )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : (edge_exists = 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (0 <= neighbor)) (PreH8 : (neighbor < vertex_count_pre)) (PreH9 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH11 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH12 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH13 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH14 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH16 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  TT && emp 
|--
  EX (visited_set2: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec scan_values2 visited_set2 ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_6_3 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : ((Znth neighbor scan_values2 0) <> 0)) (PreH2 : (edge_exists <> 0)) (PreH3 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH4 : (0 < vertex_count_pre)) (PreH5 : (vertex_count_pre < INT_MAX)) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH11 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH12 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH13 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH14 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH15 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH16 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH17 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntArray.full visited_pre vertex_count_pre scan_values2 )
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
|--
  EX (values2: (@list Z))  (visited_set2: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : ((Znth neighbor scan_values2 0) <> 0)) (PreH2 : (edge_exists <> 0)) (PreH3 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH4 : (0 < vertex_count_pre)) (PreH5 : (vertex_count_pre < INT_MAX)) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH11 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH12 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH13 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH14 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH15 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH16 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH17 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  TT && emp 
|--
  EX (visited_set2: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 ) ” 
  &&  “ (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec scan_values2 visited_set2 ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_7 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (edge_exists: Z) (visited_set2: (Z -> Prop)) (values2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 )) (PreH12 : (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 )) ,
  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values2 )
|--
  EX (values1: (@list Z))  (visited_set1: (Z -> Prop)) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (0 <= (neighbor + 1 )) ” 
  &&  “ ((neighbor + 1 ) <= vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 ) ”
  &&  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
) \/
(
forall (vertex_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (edge_exists: Z) (visited_set2: (Z -> Prop)) (values2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set2 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set2 )) (PreH12 : (safeExec (eq (visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set2 )) ,
  TT && emp 
|--
  EX (visited_set1: (Z -> Prop)) ,
  “ (0 <= (neighbor + 1 )) ” 
  &&  “ ((neighbor + 1 ) <= (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre (neighbor + 1 ) visited_set1 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 ) ” 
  &&  “ (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values2 visited_set1 ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_2Darray_entail_wit_8 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor >= vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  EX (visited_set_out: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set_out ) ” 
  &&  “ (visited_set_out vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec visited_set_out )
) \/
(
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values1: (@list Z)) (visited_set1: (Z -> Prop)) (neighbor: Z) (PreH1 : (neighbor >= vertex_count_pre)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor <= vertex_count_pre)) (PreH10 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor visited_set1 )) (PreH11 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set1 )) (PreH12 : (safeExec (eq (visited_set1)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec values1 visited_set1 )) ,
  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values1 )
|--
  EX (visited_set_out: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set_out ) ” 
  &&  “ (visited_set_out vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec visited_set_out )
).

Definition dfs_adjacency_matrix_2Darray_return_wit_1 := 
(
forall (vertex_pre: Z) (visited_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (visited_set_out: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set_out )) (PreH2 : (visited_set_out vertex_pre )) (PreH3 : (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec )) ,
  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec visited_set_out )
|--
  EX (low_visited_set: (Z -> Prop)) ,
  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec low_visited_set ) ” 
  &&  “ (low_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec low_visited_set )
) \/
(
forall (vertex_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (visited_set_out: (Z -> Prop)) (PreH1 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec visited_set_out )) (PreH2 : (visited_set_out vertex_pre )) (PreH3 : (safeExec (eq (visited_set_out)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (low_visited_set: (Z -> Prop)) ,
  “ (low_visited_set vertex_pre ) ”
  &&  emp
).

Definition dfs_adjacency_matrix_2Darray_partial_solve_wit_1 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH9 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH10 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )) ,
  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (((visited_pre + (vertex_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i visited_pre vertex_pre 0 vertex_count_pre values )
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
.

Definition dfs_adjacency_matrix_2Darray_partial_solve_wit_2 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set: (Z -> Prop)) (scan_values: (@list Z)) (row_ptr: Z) (neighbor: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH9 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set )) (PreH10 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set )) (PreH11 : (safeExec (eq (scan_visited_set)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH12 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec scan_values scan_visited_set )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntPtrArray2.missing_i matrix_pre vertex_count_pre vertex_pre row_ptr rows_low_level_spec )
  **  (((matrix_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited_pre vertex_count_pre scan_values )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set ) ” 
  &&  “ (safeExec (eq (scan_visited_set)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec scan_values scan_visited_set ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ”
  &&  (((row_ptr + (neighbor * sizeof(INT)))) # Int  |-> (Znth neighbor (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr neighbor 0 (Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i matrix_pre vertex_count_pre vertex_pre row_ptr rows_low_level_spec )
  **  (((matrix_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited_pre vertex_count_pre scan_values )
.

Definition dfs_adjacency_matrix_2Darray_partial_solve_wit_3 := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (scan_visited_set2: (Z -> Prop)) (scan_values2: (@list Z)) (neighbor: Z) (edge_exists: Z) (PreH1 : (edge_exists <> 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (0 <= neighbor)) (PreH8 : (neighbor < vertex_count_pre)) (PreH9 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH11 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 )) (PreH12 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 )) (PreH13 : (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH14 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH15 : (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 )) (PreH16 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) ,
  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre scan_values2 )
|--
  “ (edge_exists <> 0) ” 
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor scan_visited_set2 ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec scan_visited_set2 ) ” 
  &&  “ (safeExec (eq (scan_visited_set2)) (DFSAdjacencyMatrix2Darray.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec scan_values2 scan_visited_set2 ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ”
  &&  (((visited_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth neighbor scan_values2 0))
  **  (IntArray.missing_i visited_pre neighbor 0 vertex_count_pre scan_values2 )
  **  (IntPtrArray2.full matrix_pre vertex_count_pre rows_low_level_spec )
.

Definition dfs_adjacency_matrix_2Darray_partial_solve_wit_4_pure := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (edge_exists: Z) (call_visited_set: (Z -> Prop)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH11 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH12 : ~((call_visited_set neighbor ))) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH16 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec call_visited_set )) (PreH17 : (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec )) ,
  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_exists" ) )) # Int  |-> edge_exists)
  **  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec call_visited_set )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
.

Definition dfs_adjacency_matrix_2Darray_partial_solve_wit_4_aux := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (neighbor: Z) (edge_exists: Z) (call_visited_set: (Z -> Prop)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (0 <= vertex_pre)) (PreH5 : (vertex_pre < vertex_count_pre)) (PreH6 : (0 <= neighbor)) (PreH7 : (neighbor < vertex_count_pre)) (PreH8 : (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH11 : (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor )) (PreH12 : ~((call_visited_set neighbor ))) (PreH13 : (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec )) (PreH14 : ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre)) (PreH15 : (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set )) (PreH16 : (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec call_visited_set )) (PreH17 : (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec )) ,
  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec call_visited_set )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ” 
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (0 <= vertex_pre) ” 
  &&  “ (vertex_pre < vertex_count_pre) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (edge_exists = (Znth (neighbor) ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ” 
  &&  “ (ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor ) ” 
  &&  “ ~((call_visited_set neighbor )) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.adjacency_matrix_model g_low_level_spec rows_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) = vertex_count_pre) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.processed_neighbors g_low_level_spec vertex_pre neighbor call_visited_set ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec call_visited_set ) ” 
  &&  “ (safeExec (eq (call_visited_set)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyMatrix2Darray.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec call_visited_set )
.

Definition dfs_adjacency_matrix_2Darray_partial_solve_wit_4 := dfs_adjacency_matrix_2Darray_partial_solve_wit_4_pure -> dfs_adjacency_matrix_2Darray_partial_solve_wit_4_aux.

Definition dfs_adjacency_matrix_2Darray_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (X_bind_spec: (B -> ((Z -> Prop) -> Prop))) (c_bind_spec: (unit -> (@ StateRelMonad.M  (Z -> Prop) B))) (visited_set_bind_spec: (Z -> Prop)) (rows_bind_spec: (@list (@list Z))) (g_bind_spec: G) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_bind_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_bind_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_bind_spec)) (bind ((DFSAdjacencyMatrix2Darray.dfs_program (g_bind_spec) (vertex_pre))) (c_bind_spec)) X_bind_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_bind_spec rows_bind_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_bind_spec visited_set_bind_spec )
|--
EX (g_low_level_spec: G) (rows_low_level_spec: (@list (@list Z))) (visited_set_low_level_spec: (Z -> Prop)) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) ,
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec visited_set_low_level_spec ))
  **
  ((EX low_visited_set,
  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec low_visited_set ) ” 
  &&  “ (low_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec low_visited_set ))
  -*
  (EX bind_visited_set,
  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_bind_spec bind_visited_set ) ” 
  &&  “ (bind_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (bind_visited_set)) (applyf (c_bind_spec) (tt)) X_bind_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_bind_spec rows_bind_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_bind_spec bind_visited_set )))
.

Definition dfs_adjacency_matrix_2Darray_derive_high_level_spec_by_low_level_spec := 
forall (vertex_pre: Z) (visited_pre: Z) (vertex_count_pre: Z) (matrix_pre: Z) (initial_visited_set_high_level_spec: (Z -> Prop)) (g_high_level_spec: G) ,
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_high_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_high_level_spec vertex_pre ) ” 
  &&  “ (DFSAdjacencyMatrix2Darray.empty_visited initial_visited_set_high_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph matrix_pre g_high_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_high_level_spec initial_visited_set_high_level_spec )
|--
EX (g_low_level_spec: G) (rows_low_level_spec: (@list (@list Z))) (visited_set_low_level_spec: (Z -> Prop)) (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) ,
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre < INT_MAX) ” 
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ” 
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyMatrix2Darray.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec visited_set_low_level_spec ))
  **
  ((EX low_visited_set,
  “ (DFSAdjacencyMatrix2Darray.visited_extension visited_set_low_level_spec low_visited_set ) ” 
  &&  “ (low_visited_set vertex_pre ) ” 
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyMatrix2Darray.graph_rep matrix_pre g_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_low_level_spec low_visited_set ))
  -*
  (EX high_visited_set,
  “ forall (v: Z) , ((high_visited_set v ) -> (DFSAdjacencyMatrix2Darray.graph_reachable g_high_level_spec vertex_pre v )) ” 
  &&  “ forall (v_2: Z) , ((DFSAdjacencyMatrix2Darray.graph_reachable g_high_level_spec vertex_pre v_2 ) -> (high_visited_set v_2 )) ”
  &&  (DFSAdjacencyMatrix2Darray.graph matrix_pre g_high_level_spec )
  **  (DFSAdjacencyMatrix2Darray.visited visited_pre g_high_level_spec high_visited_set )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include int_ptr_array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_dfs_adjacency_matrix_2Darray_safety_wit_1 : dfs_adjacency_matrix_2Darray_safety_wit_1.
Axiom proof_of_dfs_adjacency_matrix_2Darray_safety_wit_2 : dfs_adjacency_matrix_2Darray_safety_wit_2.
Axiom proof_of_dfs_adjacency_matrix_2Darray_safety_wit_3 : dfs_adjacency_matrix_2Darray_safety_wit_3.
Axiom proof_of_dfs_adjacency_matrix_2Darray_safety_wit_4 : dfs_adjacency_matrix_2Darray_safety_wit_4.
Axiom proof_of_dfs_adjacency_matrix_2Darray_safety_wit_5 : dfs_adjacency_matrix_2Darray_safety_wit_5.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_1 : dfs_adjacency_matrix_2Darray_entail_wit_1.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_2 : dfs_adjacency_matrix_2Darray_entail_wit_2.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_3 : dfs_adjacency_matrix_2Darray_entail_wit_3.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_4 : dfs_adjacency_matrix_2Darray_entail_wit_4.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_5 : dfs_adjacency_matrix_2Darray_entail_wit_5.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_6_1 : dfs_adjacency_matrix_2Darray_entail_wit_6_1.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_6_2 : dfs_adjacency_matrix_2Darray_entail_wit_6_2.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_6_3 : dfs_adjacency_matrix_2Darray_entail_wit_6_3.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_7 : dfs_adjacency_matrix_2Darray_entail_wit_7.
Axiom proof_of_dfs_adjacency_matrix_2Darray_entail_wit_8 : dfs_adjacency_matrix_2Darray_entail_wit_8.
Axiom proof_of_dfs_adjacency_matrix_2Darray_return_wit_1 : dfs_adjacency_matrix_2Darray_return_wit_1.
Axiom proof_of_dfs_adjacency_matrix_2Darray_partial_solve_wit_1 : dfs_adjacency_matrix_2Darray_partial_solve_wit_1.
Axiom proof_of_dfs_adjacency_matrix_2Darray_partial_solve_wit_2 : dfs_adjacency_matrix_2Darray_partial_solve_wit_2.
Axiom proof_of_dfs_adjacency_matrix_2Darray_partial_solve_wit_3 : dfs_adjacency_matrix_2Darray_partial_solve_wit_3.
Axiom proof_of_dfs_adjacency_matrix_2Darray_partial_solve_wit_4_pure : dfs_adjacency_matrix_2Darray_partial_solve_wit_4_pure.
Axiom proof_of_dfs_adjacency_matrix_2Darray_partial_solve_wit_4 : dfs_adjacency_matrix_2Darray_partial_solve_wit_4.
Axiom proof_of_dfs_adjacency_matrix_2Darray_derive_bind_spec_by_low_level_spec : dfs_adjacency_matrix_2Darray_derive_bind_spec_by_low_level_spec.
Axiom proof_of_dfs_adjacency_matrix_2Darray_derive_high_level_spec_by_low_level_spec : dfs_adjacency_matrix_2Darray_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
