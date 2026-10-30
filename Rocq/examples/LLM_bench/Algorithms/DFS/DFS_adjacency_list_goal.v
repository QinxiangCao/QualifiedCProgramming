From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
From SimpleC.Verification Require Import SafeExecPrelude.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import Algorithms.DFS.DFS.
Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_list_lib.
Import ZSimpleGraph.
Local Open Scope sac.
From SimpleC.Verification Require Import safeexec_strategy_goal.
From SimpleC.Verification Require Import safeexec_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function dfs_adjacency_list -----*)

Definition dfs_adjacency_list_safety_wit_1 :=
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )),
  ((( &( "adjacency" ) )) # Ptr  |-> adjacency_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs_adjacency_list_safety_wit_2 :=
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (loop_values: (@list Z)) (loop_set: (Z -> Prop)) (done: (@list Z)) (todo: (@list Z)) (done_addrs: (@list Z)) (todo_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH8 : (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH9 : (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH10 : (row_node_addrs = (app (done_addrs) (todo_addrs)))) (PreH11 : (row = (app (done) (todo)))) (PreH12 : ((Zlength (done_addrs)) = (Zlength (done)))) (PreH13 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set )) (PreH14 : (loop_set vertex_pre )) (PreH15 : (DFSAdjacencyList.all_visited done loop_set )) (PreH16 : (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH17 : (ZSimpleGraph.visited_values g_low_level_spec loop_values loop_set )),
  ((( &( "adjacency" ) )) # Ptr  |-> adjacency_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "edge" ) )) # Ptr  |-> edge_value)
  **  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  (DFSAdjacencyList.addressed_sll edge_value todo_addrs todo )
  **  (IntArray.full visited_pre vertex_count_pre loop_values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_list_safety_wit_3 :=
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (read_set: (Z -> Prop)) (read_values: (@list Z)) (edge_value: Z) (row_head: Z) (next: Z) (row: (@list Z)) (row_node_addrs: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (done: (@list Z)) (rest: (@list Z)) (neighbor: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs)))))) (PreH15 : (row = (app (done) ((cons (neighbor) (rest)))))) (PreH16 : ((Zlength (done_addrs)) = (Zlength (done)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec read_set )) (PreH18 : (read_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited done read_set )) (PreH20 : (safeExec (eq (read_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH21 : (ZSimpleGraph.visited_values g_low_level_spec read_values read_set )),
  ((( &( "adjacency" ) )) # Ptr  |-> adjacency_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge" ) )) # Ptr  |-> edge_value)
  **  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (((visited_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth (neighbor) (read_values) (0)))
  **  (IntArray.missing_i visited_pre neighbor 0 vertex_count_pre read_values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs_adjacency_list_entail_wit_1 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )),
  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec visited_set_low_level_spec )
|--
  EX (values: (@list Z)),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )),
  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec visited_set_low_level_spec )
|--
  EX (values: (@list Z)),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
).

Definition dfs_adjacency_list_entail_wit_2 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )),
  (IntArray.full visited_pre vertex_count_pre (replace_Znth (vertex_pre) (1) (values)) )
  **  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
|--
  EX (split_values: (@list Z)) (split_set: (Z -> Prop)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec split_set ) ”
  &&  “ (split_set vertex_pre ) ”
  &&  “ (safeExec (eq (split_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec split_values split_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sll row_head row_node_addrs row )
  **  (IntArray.full visited_pre vertex_count_pre split_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (vertex_pre: Z) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )),
  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
|--
  EX (split_set: (Z -> Prop)),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec split_set ) ”
  &&  “ (split_set vertex_pre ) ”
  &&  “ (safeExec (eq (split_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec (replace_Znth (vertex_pre) (1) (values)) split_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sll (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) )
).

Definition dfs_adjacency_list_entail_wit_3 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (split_set: (Z -> Prop)) (split_values: (@list Z)) (row_head: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH8 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH9 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH10 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec split_set )) (PreH11 : (split_set vertex_pre )) (PreH12 : (safeExec (eq (split_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec split_values split_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sll row_head row_node_addrs_2 row_2 )
  **  (IntArray.full visited_pre vertex_count_pre split_values )
|--
  EX (loop_values: (@list Z)) (loop_set: (Z -> Prop)) (done: (@list Z)) (todo: (@list Z)) (done_addrs: (@list Z)) (todo_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head_2: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) (todo_addrs))) ”
  &&  “ (row = (app (done) (todo))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set ) ”
  &&  “ (loop_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done loop_set ) ”
  &&  “ (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec loop_values loop_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 row_head done_addrs done )
  **  (DFSAdjacencyList.addressed_sll row_head todo_addrs todo )
  **  (IntArray.full visited_pre vertex_count_pre loop_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (vertex_pre: Z) (split_set: (Z -> Prop)) (split_values: (@list Z)) (row_head: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH8 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH9 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH10 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec split_set )) (PreH11 : (split_set vertex_pre )) (PreH12 : (safeExec (eq (split_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH13 : (ZSimpleGraph.visited_values g_low_level_spec split_values split_set )),
  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sll row_head row_node_addrs_2 row_2 )
|--
  EX (loop_set: (Z -> Prop)) (done: (@list Z)) (todo: (@list Z)) (done_addrs: (@list Z)) (todo_addrs: (@list Z)),
  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) (todo_addrs))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) (todo))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set ) ”
  &&  “ (loop_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done loop_set ) ”
  &&  “ (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec split_values loop_set ) ”
  &&  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) row_head done_addrs done )
  **  (DFSAdjacencyList.addressed_sll row_head todo_addrs todo )
).

Definition dfs_adjacency_list_entail_wit_4 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (loop_values: (@list Z)) (loop_set: (Z -> Prop)) (done_2: (@list Z)) (todo: (@list Z)) (done_addrs_2: (@list Z)) (todo_addrs: (@list Z)) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (row_head_2: Z) (PreH1 : (edge_value <> 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH9 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH10 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH11 : (row_node_addrs_2 = (app (done_addrs_2) (todo_addrs)))) (PreH12 : (row_2 = (app (done_2) (todo)))) (PreH13 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH14 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set )) (PreH15 : (loop_set vertex_pre )) (PreH16 : (DFSAdjacencyList.all_visited done_2 loop_set )) (PreH17 : (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH18 : (ZSimpleGraph.visited_values g_low_level_spec loop_values loop_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  (DFSAdjacencyList.addressed_sll edge_value todo_addrs todo )
  **  (IntArray.full visited_pre vertex_count_pre loop_values )
|--
  EX (next: Z) (cursor_values: (@list Z)) (cursor_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z) (datum: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec datum ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= datum) ”
  &&  “ (datum < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ (row = (app (done) ((cons (datum) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec cursor_set ) ”
  &&  “ (cursor_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done cursor_set ) ”
  &&  “ (safeExec (eq (cursor_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec cursor_values cursor_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> datum)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (IntArray.full visited_pre vertex_count_pre cursor_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (vertex_pre: Z) (edge_value: Z) (loop_values: (@list Z)) (loop_set: (Z -> Prop)) (done_2: (@list Z)) (todo: (@list Z)) (done_addrs_2: (@list Z)) (todo_addrs: (@list Z)) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (row_head_2: Z) (PreH1 : (edge_value <> 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH9 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH10 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH11 : (row_node_addrs_2 = (app (done_addrs_2) (todo_addrs)))) (PreH12 : (row_2 = (app (done_2) (todo)))) (PreH13 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH14 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set )) (PreH15 : (loop_set vertex_pre )) (PreH16 : (DFSAdjacencyList.all_visited done_2 loop_set )) (PreH17 : (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH18 : (ZSimpleGraph.visited_values g_low_level_spec loop_values loop_set )),
  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  (DFSAdjacencyList.addressed_sll edge_value todo_addrs todo )
|--
  EX (next: Z) (cursor_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (datum: Z),
  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec datum ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= datum) ”
  &&  “ (datum < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) ((cons (datum) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec cursor_set ) ”
  &&  “ (cursor_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done cursor_set ) ”
  &&  “ (safeExec (eq (cursor_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec loop_values cursor_set ) ”
  &&  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> datum)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
).

Definition dfs_adjacency_list_entail_wit_5 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (cursor_set: (Z -> Prop)) (cursor_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next_2: Z) (datum: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec datum )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= datum)) (PreH9 : (datum < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH15 : (row_2 = (app (done_2) ((cons (datum) (rest_2)))))) (PreH16 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec cursor_set )) (PreH18 : (cursor_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited done_2 cursor_set )) (PreH20 : (safeExec (eq (cursor_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH21 : (ZSimpleGraph.visited_values g_low_level_spec cursor_values cursor_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> datum)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next_2)
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs_2 rest_2 )
  **  (IntArray.full visited_pre vertex_count_pre cursor_values )
|--
  EX (next: Z) (read_values: (@list Z)) (read_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec datum ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= datum) ”
  &&  “ (datum < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ (row = (app (done) ((cons (datum) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec read_set ) ”
  &&  “ (read_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done read_set ) ”
  &&  “ (safeExec (eq (read_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec read_values read_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> datum)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (((visited_pre + (datum * sizeof(INT)))) # Int  |-> (Znth (datum) (read_values) (0)))
  **  (IntArray.missing_i visited_pre datum 0 vertex_count_pre read_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (cursor_set: (Z -> Prop)) (cursor_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next_2: Z) (datum: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec datum )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= datum)) (PreH9 : (datum < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH15 : (row_2 = (app (done_2) ((cons (datum) (rest_2)))))) (PreH16 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec cursor_set )) (PreH18 : (cursor_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited done_2 cursor_set )) (PreH20 : (safeExec (eq (cursor_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH21 : (ZSimpleGraph.visited_values g_low_level_spec cursor_values cursor_set )),
  (IntArray.missing_i visited_pre datum 0 vertex_count_pre cursor_values )
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs_2 rest_2 )
|--
  EX (read_values: (@list Z)) (read_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)),
  “ ((Znth (datum) (read_values) (0)) = (Znth datum cursor_values 0)) ”
  &&  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec datum ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= datum) ”
  &&  “ (datum < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) ((cons (datum) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec read_set ) ”
  &&  “ (read_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done read_set ) ”
  &&  “ (safeExec (eq (read_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec read_values read_set ) ”
  &&  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) edge_value done_addrs done )
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs rest )
  **  (IntArray.missing_i visited_pre datum 0 vertex_count_pre read_values )
).

Definition dfs_adjacency_list_entail_wit_6 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (read_set: (Z -> Prop)) (read_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (PreH1 : ((Znth (neighbor) (read_values) (0)) = 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (0 <= neighbor)) (PreH10 : (neighbor < vertex_count_pre)) (PreH11 : (edge_value <> 0)) (PreH12 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH13 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH14 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH15 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH16 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH17 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH18 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec read_set )) (PreH19 : (read_set vertex_pre )) (PreH20 : (DFSAdjacencyList.all_visited done_2 read_set )) (PreH21 : (safeExec (eq (read_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH22 : (ZSimpleGraph.visited_values g_low_level_spec read_values read_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs_2 rest_2 )
  **  (((visited_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth (neighbor) (read_values) (0)))
  **  (IntArray.missing_i visited_pre neighbor 0 vertex_count_pre read_values )
|--
  EX (call_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ (row = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec call_set ) ”
  &&  “ (call_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done call_set ) ”
  &&  “ (safeExec (eq (call_set)) (bind ((DFSAdjacencyList.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec call_set )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (read_set: (Z -> Prop)) (read_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (PreH1 : ((Znth (neighbor) (read_values) (0)) <= INT_MAX)) (PreH2 : (neighbor <= INT_MAX)) (PreH3 : ((Znth (neighbor) (read_values) (0)) >= INT_MIN)) (PreH4 : (neighbor >= INT_MIN)) (PreH5 : ((Znth (neighbor) (read_values) (0)) = 0)) (PreH6 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH7 : (0 < vertex_count_pre)) (PreH8 : (vertex_count_pre < INT_MAX)) (PreH9 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH10 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH11 : (0 <= vertex_pre)) (PreH12 : (vertex_pre < vertex_count_pre)) (PreH13 : (0 <= neighbor)) (PreH14 : (neighbor < vertex_count_pre)) (PreH15 : (edge_value <> 0)) (PreH16 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH17 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH18 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH19 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH20 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH21 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH22 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec read_set )) (PreH23 : (read_set vertex_pre )) (PreH24 : (DFSAdjacencyList.all_visited done_2 read_set )) (PreH25 : (safeExec (eq (read_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH26 : (ZSimpleGraph.visited_values g_low_level_spec read_values read_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs_2 rest_2 )
  **  (((visited_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth (neighbor) (read_values) (0)))
  **  (IntArray.missing_i visited_pre neighbor 0 vertex_count_pre read_values )
|--
  EX (call_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec call_set ) ”
  &&  “ (call_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done call_set ) ”
  &&  “ (safeExec (eq (call_set)) (bind ((DFSAdjacencyList.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec call_set )
).

Definition dfs_adjacency_list_entail_wit_7 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (row_head_2: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (call_set: (Z -> Prop)) (bind_visited_set: (Z -> Prop)) (PreH1 : (DFSAdjacencyList.visited_extension call_set bind_visited_set )) (PreH2 : (bind_visited_set neighbor )) (PreH3 : (safeExec (eq (bind_visited_set)) (applyf ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre))) (tt)) X_low_level_spec )) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : (vertex_count_pre < INT_MAX)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH9 : (0 <= vertex_pre)) (PreH10 : (vertex_pre < vertex_count_pre)) (PreH11 : (0 <= neighbor)) (PreH12 : (neighbor < vertex_count_pre)) (PreH13 : (edge_value <> 0)) (PreH14 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH15 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH16 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH17 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH18 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH19 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH20 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec call_set )) (PreH21 : (call_set vertex_pre )) (PreH22 : (DFSAdjacencyList.all_visited done_2 call_set )),
  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec bind_visited_set )
|--
  EX (next: Z) (after_values: (@list Z)) (after_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ (row = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec after_set ) ”
  &&  “ (after_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited (app (done) ((cons (neighbor) ((@nil Z))))) after_set ) ”
  &&  “ (safeExec (eq (after_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec after_values after_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (IntArray.full visited_pre vertex_count_pre after_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (row_head_2: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (call_set: (Z -> Prop)) (bind_visited_set: (Z -> Prop)) (PreH1 : (DFSAdjacencyList.visited_extension call_set bind_visited_set )) (PreH2 : (bind_visited_set neighbor )) (PreH3 : (safeExec (eq (bind_visited_set)) (applyf ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre))) (tt)) X_low_level_spec )) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : (vertex_count_pre < INT_MAX)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH9 : (0 <= vertex_pre)) (PreH10 : (vertex_pre < vertex_count_pre)) (PreH11 : (0 <= neighbor)) (PreH12 : (neighbor < vertex_count_pre)) (PreH13 : (edge_value <> 0)) (PreH14 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH15 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH16 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH17 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH18 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH19 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH20 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec call_set )) (PreH21 : (call_set vertex_pre )) (PreH22 : (DFSAdjacencyList.all_visited done_2 call_set )),
  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec bind_visited_set )
|--
  EX (next: Z) (after_values: (@list Z)) (after_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec after_set ) ”
  &&  “ (after_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited (app (done) ((cons (neighbor) ((@nil Z))))) after_set ) ”
  &&  “ (safeExec (eq (after_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec after_values after_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (IntArray.full visited_pre vertex_count_pre after_values )
).

Definition dfs_adjacency_list_entail_wit_8_1 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (after_set: (Z -> Prop)) (after_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next_2: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH15 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH16 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec after_set )) (PreH18 : (after_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited (app (done_2) ((cons (neighbor) ((@nil Z))))) after_set )) (PreH20 : (safeExec (eq (after_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH21 : (ZSimpleGraph.visited_values g_low_level_spec after_values after_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next_2)
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs_2 rest_2 )
  **  (IntArray.full visited_pre vertex_count_pre after_values )
|--
  EX (next: Z) (next_values: (@list Z)) (next_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ (row = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec next_set ) ”
  &&  “ (next_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited (app (done) ((cons (neighbor) ((@nil Z))))) next_set ) ”
  &&  “ (safeExec (eq (next_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec next_values next_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (IntArray.full visited_pre vertex_count_pre next_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (vertex_pre: Z) (after_set: (Z -> Prop)) (after_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next_2: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH15 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH16 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec after_set )) (PreH18 : (after_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited (app (done_2) ((cons (neighbor) ((@nil Z))))) after_set )) (PreH20 : (safeExec (eq (after_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH21 : (ZSimpleGraph.visited_values g_low_level_spec after_values after_set )),
  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs_2 rest_2 )
|--
  EX (next_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)),
  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec next_set ) ”
  &&  “ (next_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited (app (done) ((cons (neighbor) ((@nil Z))))) next_set ) ”
  &&  “ (safeExec (eq (next_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec after_values next_set ) ”
  &&  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) edge_value done_addrs done )
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs rest )
).

Definition dfs_adjacency_list_entail_wit_8_2 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (read_set: (Z -> Prop)) (read_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next_2: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (PreH1 : ((Znth (neighbor) (read_values) (0)) <> 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH7 : (0 <= vertex_pre)) (PreH8 : (vertex_pre < vertex_count_pre)) (PreH9 : (0 <= neighbor)) (PreH10 : (neighbor < vertex_count_pre)) (PreH11 : (edge_value <> 0)) (PreH12 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH13 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH14 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH15 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH16 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH17 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH18 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec read_set )) (PreH19 : (read_set vertex_pre )) (PreH20 : (DFSAdjacencyList.all_visited done_2 read_set )) (PreH21 : (safeExec (eq (read_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH22 : (ZSimpleGraph.visited_values g_low_level_spec read_values read_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next_2)
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs_2 rest_2 )
  **  (((visited_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth (neighbor) (read_values) (0)))
  **  (IntArray.missing_i visited_pre neighbor 0 vertex_count_pre read_values )
|--
  EX (next: Z) (next_values: (@list Z)) (next_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ (row = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec next_set ) ”
  &&  “ (next_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited (app (done) ((cons (neighbor) ((@nil Z))))) next_set ) ”
  &&  “ (safeExec (eq (next_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec next_values next_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (IntArray.full visited_pre vertex_count_pre next_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (read_set: (Z -> Prop)) (read_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next_2: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs_2: (@list Z)) (done_2: (@list Z)) (rest_2: (@list Z)) (neighbor: Z) (PreH1 : ((Znth (neighbor) (read_values) (0)) <= INT_MAX)) (PreH2 : ((Znth (neighbor) (read_values) (0)) >= INT_MIN)) (PreH3 : ((Znth (neighbor) (read_values) (0)) <> 0)) (PreH4 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH5 : (0 < vertex_count_pre)) (PreH6 : (vertex_count_pre < INT_MAX)) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH8 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH9 : (0 <= vertex_pre)) (PreH10 : (vertex_pre < vertex_count_pre)) (PreH11 : (0 <= neighbor)) (PreH12 : (neighbor < vertex_count_pre)) (PreH13 : (edge_value <> 0)) (PreH14 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH15 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH16 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH17 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs_2)))))) (PreH18 : (row_2 = (app (done_2) ((cons (neighbor) (rest_2)))))) (PreH19 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH20 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec read_set )) (PreH21 : (read_set vertex_pre )) (PreH22 : (DFSAdjacencyList.all_visited done_2 read_set )) (PreH23 : (safeExec (eq (read_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH24 : (ZSimpleGraph.visited_values g_low_level_spec read_values read_set )),
  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs_2 rest_2 )
  **  (((visited_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth (neighbor) (read_values) (0)))
  **  (IntArray.missing_i visited_pre neighbor 0 vertex_count_pre read_values )
|--
  EX (next_values: (@list Z)) (next_set: (Z -> Prop)) (done: (@list Z)) (rest: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)),
  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec next_set ) ”
  &&  “ (next_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited (app (done) ((cons (neighbor) ((@nil Z))))) next_set ) ”
  &&  “ (safeExec (eq (next_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec next_values next_set ) ”
  &&  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) edge_value done_addrs done )
  **  (DFSAdjacencyList.addressed_sll next_2 rest_addrs rest )
  **  (IntArray.full visited_pre vertex_count_pre next_values )
).

Definition dfs_adjacency_list_entail_wit_9 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (next_set: (Z -> Prop)) (next_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs: (@list Z)) (done_2: (@list Z)) (rest: (@list Z)) (neighbor: Z) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs)))))) (PreH15 : (row_2 = (app (done_2) ((cons (neighbor) (rest)))))) (PreH16 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec next_set )) (PreH18 : (next_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited (app (done_2) ((cons (neighbor) ((@nil Z))))) next_set )) (PreH20 : (safeExec (eq (next_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH21 : (ZSimpleGraph.visited_values g_low_level_spec next_values next_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head_2)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
  **  (IntArray.full visited_pre vertex_count_pre next_values )
|--
  EX (loop_values: (@list Z)) (loop_set: (Z -> Prop)) (done: (@list Z)) (todo: (@list Z)) (done_addrs: (@list Z)) (todo_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z),
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) (todo_addrs))) ”
  &&  “ (row = (app (done) (todo))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set ) ”
  &&  “ (loop_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done loop_set ) ”
  &&  “ (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec loop_values loop_set ) ”
  &&  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head next done_addrs done )
  **  (DFSAdjacencyList.addressed_sll next todo_addrs todo )
  **  (IntArray.full visited_pre vertex_count_pre loop_values )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (vertex_pre: Z) (next_set: (Z -> Prop)) (next_values: (@list Z)) (edge_value: Z) (row_head_2: Z) (next: Z) (row_2: (@list Z)) (row_node_addrs_2: (@list Z)) (done_addrs_2: (@list Z)) (rest_addrs: (@list Z)) (done_2: (@list Z)) (rest: (@list Z)) (neighbor: Z) (PreH1 : (neighbor <= INT_MAX)) (PreH2 : (neighbor >= INT_MIN)) (PreH3 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH4 : (0 < vertex_count_pre)) (PreH5 : (vertex_count_pre < INT_MAX)) (PreH6 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH7 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH8 : (0 <= vertex_pre)) (PreH9 : (vertex_pre < vertex_count_pre)) (PreH10 : (0 <= neighbor)) (PreH11 : (neighbor < vertex_count_pre)) (PreH12 : (edge_value <> 0)) (PreH13 : (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH14 : (row_node_addrs_2 = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH15 : (row_2 = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH16 : (row_node_addrs_2 = (app (done_addrs_2) ((cons (edge_value) (rest_addrs)))))) (PreH17 : (row_2 = (app (done_2) ((cons (neighbor) (rest)))))) (PreH18 : ((Zlength (done_addrs_2)) = (Zlength (done_2)))) (PreH19 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec next_set )) (PreH20 : (next_set vertex_pre )) (PreH21 : (DFSAdjacencyList.all_visited (app (done_2) ((cons (neighbor) ((@nil Z))))) next_set )) (PreH22 : (safeExec (eq (next_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH23 : (ZSimpleGraph.visited_values g_low_level_spec next_values next_set )),
  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head_2 edge_value done_addrs_2 done_2 )
  **  ((&((edge_value)  # "list" ->ₛ "data")) # Int  |-> neighbor)
  **  ((&((edge_value)  # "list" ->ₛ "next")) # Ptr  |-> next)
  **  (DFSAdjacencyList.addressed_sll next rest_addrs rest )
|--
  EX (loop_set: (Z -> Prop)) (done: (@list Z)) (todo: (@list Z)) (done_addrs: (@list Z)) (todo_addrs: (@list Z)),
  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_head_2 = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ ((Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))) = (app (done_addrs) (todo_addrs))) ”
  &&  “ ((Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))) = (app (done) (todo))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set ) ”
  &&  “ (loop_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done loop_set ) ”
  &&  “ (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec next_values loop_set ) ”
  &&  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)) next done_addrs done )
  **  (DFSAdjacencyList.addressed_sll next todo_addrs todo )
).

Definition dfs_adjacency_list_return_wit_1 :=
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (loop_values: (@list Z)) (loop_set: (Z -> Prop)) (done: (@list Z)) (todo: (@list Z)) (done_addrs: (@list Z)) (todo_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z) (PreH1 : (edge_value = 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH9 : (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH10 : (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH11 : (row_node_addrs = (app (done_addrs) (todo_addrs)))) (PreH12 : (row = (app (done) (todo)))) (PreH13 : ((Zlength (done_addrs)) = (Zlength (done)))) (PreH14 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set )) (PreH15 : (loop_set vertex_pre )) (PreH16 : (DFSAdjacencyList.all_visited done loop_set )) (PreH17 : (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH18 : (ZSimpleGraph.visited_values g_low_level_spec loop_values loop_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  (DFSAdjacencyList.addressed_sll edge_value todo_addrs todo )
  **  (IntArray.full visited_pre vertex_count_pre loop_values )
|--
  EX (low_visited_set: (Z -> Prop)),
  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec low_visited_set ) ”
  &&  “ (low_visited_set vertex_pre ) ”
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec low_visited_set )
) \/
(
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (loop_values: (@list Z)) (loop_set: (Z -> Prop)) (done: (@list Z)) (todo: (@list Z)) (done_addrs: (@list Z)) (todo_addrs: (@list Z)) (row: (@list Z)) (row_node_addrs: (@list Z)) (row_head: Z) (PreH1 : (edge_value = 0)) (PreH2 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH3 : (0 < vertex_count_pre)) (PreH4 : (vertex_count_pre < INT_MAX)) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH9 : (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH10 : (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH11 : (row_node_addrs = (app (done_addrs) (todo_addrs)))) (PreH12 : (row = (app (done) (todo)))) (PreH13 : ((Zlength (done_addrs)) = (Zlength (done)))) (PreH14 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec loop_set )) (PreH15 : (loop_set vertex_pre )) (PreH16 : (DFSAdjacencyList.all_visited done loop_set )) (PreH17 : (safeExec (eq (loop_set)) (DFSAdjacencyList.dfs_loop (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH18 : (ZSimpleGraph.visited_values g_low_level_spec loop_values loop_set )),
  (((adjacency_pre + (vertex_pre * sizeof(PTR)))) # Ptr  |-> row_head)
  **  (DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec vertex_pre )
  **  (DFSAdjacencyList.addressed_sllseg row_head edge_value done_addrs done )
  **  (DFSAdjacencyList.addressed_sll edge_value todo_addrs todo )
  **  (IntArray.full visited_pre vertex_count_pre loop_values )
|--
  EX (low_visited_set: (Z -> Prop)),
  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec low_visited_set ) ”
  &&  “ (low_visited_set vertex_pre ) ”
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec low_visited_set )
).

Definition dfs_adjacency_list_partial_solve_wit_1 :=
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (values: (@list Z)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (0 <= vertex_pre)) (PreH6 : (vertex_pre < vertex_count_pre)) (PreH7 : (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec )) (PreH8 : (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec )),
  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (IntArray.full visited_pre vertex_count_pre values )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  “ (ZSimpleGraph.visited_values g_low_level_spec values visited_set_low_level_spec ) ”
  &&  (((visited_pre + (vertex_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i visited_pre vertex_pre 0 vertex_count_pre values )
  **  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
.

Definition dfs_adjacency_list_partial_solve_wit_2_pure :=
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (row_head: Z) (row: (@list Z)) (row_node_addrs: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (done: (@list Z)) (rest: (@list Z)) (neighbor: Z) (call_set: (Z -> Prop)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs)))))) (PreH15 : (row = (app (done) ((cons (neighbor) (rest)))))) (PreH16 : ((Zlength (done_addrs)) = (Zlength (done)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec call_set )) (PreH18 : (call_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited done call_set )) (PreH20 : (safeExec (eq (call_set)) (bind ((DFSAdjacencyList.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec )),
  ((( &( "adjacency" ) )) # Ptr  |-> adjacency_pre)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited_pre)
  **  ((( &( "vertex" ) )) # Int  |-> vertex_pre)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge" ) )) # Ptr  |-> edge_value)
  **  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec call_set )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (safeExec (eq (call_set)) (bind ((DFSAdjacencyList.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
.

Definition dfs_adjacency_list_partial_solve_wit_2_aux :=
forall (X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))) (visited_set_low_level_spec: (Z -> Prop)) (rows_low_level_spec: (@list (@list Z))) (node_addrs_low_level_spec: (@list (@list Z))) (row_ptrs_low_level_spec: (@list Z)) (g_low_level_spec: G) (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (edge_value: Z) (row_head: Z) (row: (@list Z)) (row_node_addrs: (@list Z)) (done_addrs: (@list Z)) (rest_addrs: (@list Z)) (done: (@list Z)) (rest: (@list Z)) (neighbor: Z) (call_set: (Z -> Prop)) (PreH1 : (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec)))) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre < INT_MAX)) (PreH4 : (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre )) (PreH5 : (ZSimpleGraph.vertex_valid g_low_level_spec neighbor )) (PreH6 : (0 <= vertex_pre)) (PreH7 : (vertex_pre < vertex_count_pre)) (PreH8 : (0 <= neighbor)) (PreH9 : (neighbor < vertex_count_pre)) (PreH10 : (edge_value <> 0)) (PreH11 : (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0)))) (PreH12 : (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z))))) (PreH13 : (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z))))) (PreH14 : (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs)))))) (PreH15 : (row = (app (done) ((cons (neighbor) (rest)))))) (PreH16 : ((Zlength (done_addrs)) = (Zlength (done)))) (PreH17 : (DFSAdjacencyList.visited_extension visited_set_low_level_spec call_set )) (PreH18 : (call_set vertex_pre )) (PreH19 : (DFSAdjacencyList.all_visited done call_set )) (PreH20 : (safeExec (eq (call_set)) (bind ((DFSAdjacencyList.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec )),
  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec call_set )
|--
  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (safeExec (eq (call_set)) (bind ((DFSAdjacencyList.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  “ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec neighbor ) ”
  &&  “ (0 <= vertex_pre) ”
  &&  “ (vertex_pre < vertex_count_pre) ”
  &&  “ (0 <= neighbor) ”
  &&  “ (neighbor < vertex_count_pre) ”
  &&  “ (edge_value <> 0) ”
  &&  “ (row_head = (Znth (vertex_pre) (row_ptrs_low_level_spec) (0))) ”
  &&  “ (row_node_addrs = (Znth (vertex_pre) (node_addrs_low_level_spec) ((@nil Z)))) ”
  &&  “ (row = (Znth (vertex_pre) (rows_low_level_spec) ((@nil Z)))) ”
  &&  “ (row_node_addrs = (app (done_addrs) ((cons (edge_value) (rest_addrs))))) ”
  &&  “ (row = (app (done) ((cons (neighbor) (rest))))) ”
  &&  “ ((Zlength (done_addrs)) = (Zlength (done))) ”
  &&  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec call_set ) ”
  &&  “ (call_set vertex_pre ) ”
  &&  “ (DFSAdjacencyList.all_visited done call_set ) ”
  &&  “ (safeExec (eq (call_set)) (bind ((DFSAdjacencyList.dfs_program (g_low_level_spec) (neighbor))) ((DFSAdjacencyList.dfs_continue (g_low_level_spec) (vertex_pre)))) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec call_set )
.

Definition dfs_adjacency_list_partial_solve_wit_2 := dfs_adjacency_list_partial_solve_wit_2_pure -> dfs_adjacency_list_partial_solve_wit_2_aux.

(* Shallow FunAssertion specs for dfs_adjacency_list. *)
Definition dfs_adjacency_list_sig : FuncSig := ([ *  * struct "list"; i32;  * i32; i32], void)%ctype.

Definition dfs_adjacency_list_low_level_spec : Spec dfs_adjacency_list_sig :=
  fun F =>
ALL (g: G),
ALL (row_ptrs: (@list Z)),
ALL (node_addrs: (@list (@list Z))),
ALL (rows: (@list (@list Z))),
ALL (visited_set: (Z -> Prop)),
ALL (X: (unit -> ((Z -> Prop) -> Prop))),
HoareFun ([ *  * struct "list"; i32;  * i32; i32], void)%ctype
  (fun '(adjacency_pre, (vertex_count_pre, (visited_pre, vertex_pre))) =>
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g vertex_pre ) ”
  &&  “ (safeExec (eq (visited_set)) (DFSAdjacencyList.dfs_program (g) (vertex_pre)) X ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g row_ptrs node_addrs rows )
  **  (DFSAdjacencyList.visited visited_pre g visited_set )))
  (fun '(adjacency_pre, (vertex_count_pre, (visited_pre, vertex_pre))) (_retval : unit) =>
  (EX (low_visited_set: (Z -> Prop)),
  “ (DFSAdjacencyList.visited_extension visited_set low_visited_set ) ”
  &&  “ (low_visited_set vertex_pre ) ”
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g row_ptrs node_addrs rows )
  **  (DFSAdjacencyList.visited visited_pre g low_visited_set )))
  F.

Definition dfs_adjacency_list_bind_spec : Spec dfs_adjacency_list_sig :=
  fun F =>
ALL B : Type,
ALL (g: G),
ALL (row_ptrs: (@list Z)),
ALL (node_addrs: (@list (@list Z))),
ALL (rows: (@list (@list Z))),
ALL (visited_set: (Z -> Prop)),
ALL (c: (unit -> (@ StateRelMonad.M  (Z -> Prop) B))),
ALL (X: (B -> ((Z -> Prop) -> Prop))),
HoareFun ([ *  * struct "list"; i32;  * i32; i32], void)%ctype
  (fun '(adjacency_pre, (vertex_count_pre, (visited_pre, vertex_pre))) =>
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g vertex_pre ) ”
  &&  “ (safeExec (eq (visited_set)) (bind ((DFSAdjacencyList.dfs_program (g) (vertex_pre))) (c)) X ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g row_ptrs node_addrs rows )
  **  (DFSAdjacencyList.visited visited_pre g visited_set )))
  (fun '(adjacency_pre, (vertex_count_pre, (visited_pre, vertex_pre))) (_retval : unit) =>
  (EX (bind_visited_set: (Z -> Prop)),
  “ (DFSAdjacencyList.visited_extension visited_set bind_visited_set ) ”
  &&  “ (bind_visited_set vertex_pre ) ”
  &&  “ (safeExec (eq (bind_visited_set)) (applyf (c) (tt)) X ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g row_ptrs node_addrs rows )
  **  (DFSAdjacencyList.visited visited_pre g bind_visited_set )))
  F.

Definition dfs_adjacency_list_high_level_spec : Spec dfs_adjacency_list_sig :=
  fun F =>
ALL (g: G),
ALL (initial_visited_set: (Z -> Prop)),
HoareFun ([ *  * struct "list"; i32;  * i32; i32], void)%ctype
  (fun '(adjacency_pre, (vertex_count_pre, (visited_pre, vertex_pre))) =>
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g vertex_pre ) ”
  &&  “ (DFSAdjacencyList.empty_visited initial_visited_set ) ”
  &&  (DFSAdjacencyList.graph adjacency_pre g )
  **  (DFSAdjacencyList.visited visited_pre g initial_visited_set )))
  (fun '(adjacency_pre, (vertex_count_pre, (visited_pre, vertex_pre))) (_retval : unit) =>
  (EX (high_visited_set: (Z -> Prop)),
  “ forall (v: Z), ((high_visited_set v ) -> (DFSAdjacencyList.is_reachable g vertex_pre v )) ”
  &&  “ forall (v_2: Z), ((DFSAdjacencyList.is_reachable g vertex_pre v_2 ) -> (high_visited_set v_2 )) ”
  &&  (DFSAdjacencyList.graph adjacency_pre g )
  **  (DFSAdjacencyList.visited visited_pre g high_visited_set )))
  F.

Definition dfs_adjacency_list_low_level_spec_entail_bind_spec :=
forall (B: Type),
forall (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (g_bind_spec: G) (row_ptrs_bind_spec: (@list Z)) (node_addrs_bind_spec: (@list (@list Z))) (rows_bind_spec: (@list (@list Z))) (visited_set_bind_spec: (Z -> Prop)) (c_bind_spec: (unit -> (@ StateRelMonad.M  (Z -> Prop) B))) (X_bind_spec: (B -> ((Z -> Prop) -> Prop))),
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_bind_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_bind_spec vertex_pre ) ”
  &&  “ (safeExec (eq (visited_set_bind_spec)) (bind ((DFSAdjacencyList.dfs_program (g_bind_spec) (vertex_pre))) (c_bind_spec)) X_bind_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_bind_spec row_ptrs_bind_spec node_addrs_bind_spec rows_bind_spec )
  **  (DFSAdjacencyList.visited visited_pre g_bind_spec visited_set_bind_spec ))
|--
EX (g_low_level_spec: G)(row_ptrs_low_level_spec: (@list Z))(node_addrs_low_level_spec: (@list (@list Z)))(rows_low_level_spec: (@list (@list Z)))(visited_set_low_level_spec: (Z -> Prop))(X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))),
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec visited_set_low_level_spec ))
  **
  (  (EX (low_visited_set: (Z -> Prop)),
  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec low_visited_set ) ”
  &&  “ (low_visited_set vertex_pre ) ”
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec low_visited_set ))
  -*
  (EX (bind_visited_set: (Z -> Prop)),
  “ (DFSAdjacencyList.visited_extension visited_set_bind_spec bind_visited_set ) ”
  &&  “ (bind_visited_set vertex_pre ) ”
  &&  “ (safeExec (eq (bind_visited_set)) (applyf (c_bind_spec) (tt)) X_bind_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_bind_spec row_ptrs_bind_spec node_addrs_bind_spec rows_bind_spec )
  **  (DFSAdjacencyList.visited visited_pre g_bind_spec bind_visited_set )))
.

Definition dfs_adjacency_list_low_level_spec_entail_high_level_spec :=
forall (adjacency_pre: Z) (vertex_count_pre: Z) (visited_pre: Z) (vertex_pre: Z) (g_high_level_spec: G) (initial_visited_set_high_level_spec: (Z -> Prop)),
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_high_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_high_level_spec vertex_pre ) ”
  &&  “ (DFSAdjacencyList.empty_visited initial_visited_set_high_level_spec ) ”
  &&  (DFSAdjacencyList.graph adjacency_pre g_high_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_high_level_spec initial_visited_set_high_level_spec ))
|--
EX (g_low_level_spec: G)(row_ptrs_low_level_spec: (@list Z))(node_addrs_low_level_spec: (@list (@list Z)))(rows_low_level_spec: (@list (@list Z)))(visited_set_low_level_spec: (Z -> Prop))(X_low_level_spec: (unit -> ((Z -> Prop) -> Prop))),
  (“ (vertex_count_pre = (ZSimpleGraph.vertex_count (g_low_level_spec))) ”
  &&  “ (0 < vertex_count_pre) ”
  &&  “ (vertex_count_pre < INT_MAX) ”
  &&  “ (ZSimpleGraph.vertex_valid g_low_level_spec vertex_pre ) ”
  &&  “ (safeExec (eq (visited_set_low_level_spec)) (DFSAdjacencyList.dfs_program (g_low_level_spec) (vertex_pre)) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec visited_set_low_level_spec ))
  **
  (  (EX (low_visited_set: (Z -> Prop)),
  “ (DFSAdjacencyList.visited_extension visited_set_low_level_spec low_visited_set ) ”
  &&  “ (low_visited_set vertex_pre ) ”
  &&  “ (safeExec (eq (low_visited_set)) (return (tt)) X_low_level_spec ) ”
  &&  (DFSAdjacencyList.store_graph adjacency_pre g_low_level_spec row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_low_level_spec low_visited_set ))
  -*
  (EX (high_visited_set: (Z -> Prop)),
  “ forall (v: Z), ((high_visited_set v ) -> (DFSAdjacencyList.is_reachable g_high_level_spec vertex_pre v )) ”
  &&  “ forall (v_2: Z), ((DFSAdjacencyList.is_reachable g_high_level_spec vertex_pre v_2 ) -> (high_visited_set v_2 )) ”
  &&  (DFSAdjacencyList.graph adjacency_pre g_high_level_spec )
  **  (DFSAdjacencyList.visited visited_pre g_high_level_spec high_visited_set )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_dfs_adjacency_list_safety_wit_1 : dfs_adjacency_list_safety_wit_1.
Axiom proof_of_dfs_adjacency_list_safety_wit_2 : dfs_adjacency_list_safety_wit_2.
Axiom proof_of_dfs_adjacency_list_safety_wit_3 : dfs_adjacency_list_safety_wit_3.
Axiom proof_of_dfs_adjacency_list_entail_wit_1 : dfs_adjacency_list_entail_wit_1.
Axiom proof_of_dfs_adjacency_list_entail_wit_2 : dfs_adjacency_list_entail_wit_2.
Axiom proof_of_dfs_adjacency_list_entail_wit_3 : dfs_adjacency_list_entail_wit_3.
Axiom proof_of_dfs_adjacency_list_entail_wit_4 : dfs_adjacency_list_entail_wit_4.
Axiom proof_of_dfs_adjacency_list_entail_wit_5 : dfs_adjacency_list_entail_wit_5.
Axiom proof_of_dfs_adjacency_list_entail_wit_6 : dfs_adjacency_list_entail_wit_6.
Axiom proof_of_dfs_adjacency_list_entail_wit_7 : dfs_adjacency_list_entail_wit_7.
Axiom proof_of_dfs_adjacency_list_entail_wit_8_1 : dfs_adjacency_list_entail_wit_8_1.
Axiom proof_of_dfs_adjacency_list_entail_wit_8_2 : dfs_adjacency_list_entail_wit_8_2.
Axiom proof_of_dfs_adjacency_list_entail_wit_9 : dfs_adjacency_list_entail_wit_9.
Axiom proof_of_dfs_adjacency_list_return_wit_1 : dfs_adjacency_list_return_wit_1.
Axiom proof_of_dfs_adjacency_list_partial_solve_wit_1 : dfs_adjacency_list_partial_solve_wit_1.
Axiom proof_of_dfs_adjacency_list_partial_solve_wit_2_pure : dfs_adjacency_list_partial_solve_wit_2_pure.
Axiom proof_of_dfs_adjacency_list_partial_solve_wit_2 : dfs_adjacency_list_partial_solve_wit_2.
Axiom proof_of_dfs_adjacency_list_low_level_spec_entail_bind_spec : dfs_adjacency_list_low_level_spec_entail_bind_spec.
Axiom proof_of_dfs_adjacency_list_low_level_spec_entail_high_level_spec : dfs_adjacency_list_low_level_spec_entail_high_level_spec.

End VC_Correct.
