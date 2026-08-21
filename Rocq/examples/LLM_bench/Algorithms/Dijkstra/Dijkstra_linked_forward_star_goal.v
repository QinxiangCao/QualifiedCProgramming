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
Require Import Algorithms.Dijkstra.Dijkstra.
Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_lib.
Import DijkstraGraph.
Import DijkstraLinkedForwardStar.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function dijkstra_linked_forward_star_init -----*)

Definition dijkstra_linked_forward_star_init_safety_wit_1 := 
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist0: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (vector_shape dist0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full dist_pre 10 dist0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_init_safety_wit_2 := 
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_cur: (@list Z)) (i: Z) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= 10)) (PreH7 : (dist_init_loop i dist_cur )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dist_pre 10 dist_cur )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition dijkstra_linked_forward_star_init_safety_wit_3 := 
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_cur: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dist_pre 10 dist_cur )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition dijkstra_linked_forward_star_init_safety_wit_4 := 
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_cur: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur )) ,
  (IntArray.full dist_pre 10 (replace_Znth (i) (1000000000) (dist_cur)) )
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dijkstra_linked_forward_star_init_safety_wit_5 := 
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_all_inf: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (dist_init_loop 10 dist_all_inf )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full dist_pre 10 dist_all_inf )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_init_entail_wit_1 := 
(
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist0: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (vector_shape dist0 )) ,
  (IntArray.full dist_pre 10 dist0 )
|--
  EX (dist_cur: (@list Z)) ,
  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ (dist_init_loop 0 dist_cur ) ”
  &&  (IntArray.full dist_pre 10 dist_cur )
) \/
(
forall (source_pre: Z) (vertex_count_pre: Z) (dist0: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (vector_shape dist0 )) ,
  TT && emp 
|--
  “ (dist_init_loop 0 dist0 ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_init_entail_wit_1_split_goal_1 := 
forall (source_pre: Z) (vertex_count_pre: Z) (dist0: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (vector_shape dist0 )) ,
  (dist_init_loop 0 dist0 )
.

Definition dijkstra_linked_forward_star_init_entail_wit_2 := 
(
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_cur_2: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur_2 )) ,
  (IntArray.full dist_pre 10 (replace_Znth (i) (1000000000) (dist_cur_2)) )
|--
  EX (dist_cur: (@list Z)) ,
  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 10) ” 
  &&  “ (dist_init_loop (i + 1 ) dist_cur ) ”
  &&  (IntArray.full dist_pre 10 dist_cur )
) \/
(
forall (source_pre: Z) (vertex_count_pre: Z) (dist_cur_2: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur_2 )) ,
  TT && emp 
|--
  “ (dist_init_loop (i + 1 ) (replace_Znth (i) (1000000000) (dist_cur_2)) ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_init_entail_wit_2_split_goal_1 := 
forall (source_pre: Z) (vertex_count_pre: Z) (dist_cur_2: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur_2 )) ,
  (dist_init_loop (i + 1 ) (replace_Znth (i) (1000000000) (dist_cur_2)) )
.

Definition dijkstra_linked_forward_star_init_entail_wit_3 := 
(
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_cur: (@list Z)) (i: Z) (PreH1 : (i >= 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur )) ,
  (IntArray.full dist_pre 10 dist_cur )
|--
  EX (dist_all_inf: (@list Z)) ,
  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (dist_init_loop 10 dist_all_inf ) ”
  &&  (IntArray.full dist_pre 10 dist_all_inf )
) \/
(
forall (source_pre: Z) (vertex_count_pre: Z) (dist_cur: (@list Z)) (i: Z) (PreH1 : (i >= 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur )) ,
  TT && emp 
|--
  “ (dist_init_loop 10 dist_cur ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_init_entail_wit_3_split_goal_1 := 
forall (source_pre: Z) (vertex_count_pre: Z) (dist_cur: (@list Z)) (i: Z) (PreH1 : (i >= 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur )) ,
  (dist_init_loop 10 dist_cur )
.

Definition dijkstra_linked_forward_star_init_return_wit_1 := 
(
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_all_inf: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (dist_init_loop 10 dist_all_inf )) ,
  (IntArray.full dist_pre 10 (replace_Znth (source_pre) (0) (dist_all_inf)) )
|--
  EX (dist1: (@list Z)) ,
  “ (dijkstra_init_dist vertex_count_pre source_pre dist1 ) ”
  &&  (IntArray.full dist_pre 10 dist1 )
) \/
(
forall (source_pre: Z) (vertex_count_pre: Z) (dist_all_inf: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (dist_init_loop 10 dist_all_inf )) ,
  TT && emp 
|--
  “ (dijkstra_init_dist vertex_count_pre source_pre (replace_Znth (source_pre) (0) (dist_all_inf)) ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_init_return_wit_1_split_goal_1 := 
forall (source_pre: Z) (vertex_count_pre: Z) (dist_all_inf: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (dist_init_loop 10 dist_all_inf )) ,
  (dijkstra_init_dist vertex_count_pre source_pre (replace_Znth (source_pre) (0) (dist_all_inf)) )
.

Definition dijkstra_linked_forward_star_init_partial_solve_wit_1 := 
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_cur: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 < vertex_count_pre)) (PreH3 : (vertex_count_pre <= 10)) (PreH4 : (0 <= source_pre)) (PreH5 : (source_pre < vertex_count_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= 10)) (PreH8 : (dist_init_loop i dist_cur )) ,
  (IntArray.full dist_pre 10 dist_cur )
|--
  “ (i < 10) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 10) ” 
  &&  “ (dist_init_loop i dist_cur ) ”
  &&  (((dist_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre i 0 10 dist_cur )
.

Definition dijkstra_linked_forward_star_init_partial_solve_wit_2 := 
forall (dist_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist_all_inf: (@list Z)) (PreH1 : (0 < vertex_count_pre)) (PreH2 : (vertex_count_pre <= 10)) (PreH3 : (0 <= source_pre)) (PreH4 : (source_pre < vertex_count_pre)) (PreH5 : (dist_init_loop 10 dist_all_inf )) ,
  (IntArray.full dist_pre 10 dist_all_inf )
|--
  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (dist_init_loop 10 dist_all_inf ) ”
  &&  (((dist_pre + (source_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre source_pre 0 10 dist_all_inf )
.

(*----- Function dijkstra_linked_forward_star -----*)

Definition dijkstra_linked_forward_star_safety_wit_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH6 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH7 : (visited_set_empty visited_init )) (PreH8 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH9 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_safety_wit_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_items: (@list (Z * Z))) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) (PreH3 : (retval = 1)) (PreH4 : ((Zlength (queue_items)) = 0)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH8 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH9 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH10 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH11 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_safety_wit_3 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_items: (@list (Z * Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) (PreH3 : (retval = 0)) (PreH4 : ((Zlength (queue_items)) <> 0)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH8 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH9 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH10 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH11 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_safety_wit_4 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (0 <= cur_vertex)) (PreH6 : (cur_vertex < vertex_count_pre)) (PreH7 : (0 <= cur_distance)) (PreH8 : (cur_distance <= 1000000000)) (PreH9 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH10 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH11 : (0 <= edge)) (PreH12 : (edge < edge_count_pre)) (PreH13 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (1 <> (INT_MIN)) ”
.

Definition dijkstra_linked_forward_star_safety_wit_5 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (0 <= cur_vertex)) (PreH6 : (cur_vertex < vertex_count_pre)) (PreH7 : (0 <= cur_distance)) (PreH8 : (cur_distance <= 1000000000)) (PreH9 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH10 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH11 : (edge = (-1))) (PreH12 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH13 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (1 <> (INT_MIN)) ”
.

Definition dijkstra_linked_forward_star_safety_wit_6 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (0 <= cur_vertex)) (PreH6 : (cur_vertex < vertex_count_pre)) (PreH7 : (0 <= cur_distance)) (PreH8 : (cur_distance <= 1000000000)) (PreH9 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH10 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH11 : (edge = (-1))) (PreH12 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH13 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dijkstra_linked_forward_star_safety_wit_7 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (0 <= cur_vertex)) (PreH6 : (cur_vertex < vertex_count_pre)) (PreH7 : (0 <= cur_distance)) (PreH8 : (cur_distance <= 1000000000)) (PreH9 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH10 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH11 : (0 <= edge)) (PreH12 : (edge < edge_count_pre)) (PreH13 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dijkstra_linked_forward_star_safety_wit_8 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge <> (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH12 : (edge = (-1))) (PreH13 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_safety_wit_9 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge = (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH15 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_safety_wit_10 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (0 <= cur_vertex)) (PreH6 : (cur_vertex < vertex_count_pre)) (PreH7 : (0 <= cur_distance)) (PreH8 : (cur_distance <= 1000000000)) (PreH9 : (0 <= edge)) (PreH10 : (edge < edge_count_pre)) (PreH11 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH12 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH13 : (0 <= neighbor)) (PreH14 : (neighbor < vertex_count_pre)) (PreH15 : (neighbor < 10)) (PreH16 : (0 <= edge_weight)) (PreH17 : (edge_weight <= 1000000000)) (PreH18 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH19 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH20 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH21 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_safety_wit_11 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (edge_weight < 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (0 <= edge)) (PreH11 : (edge < edge_count_pre)) (PreH12 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH13 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH14 : (0 <= neighbor)) (PreH15 : (neighbor < vertex_count_pre)) (PreH16 : (neighbor < 10)) (PreH17 : (0 <= edge_weight)) (PreH18 : (edge_weight <= 1000000000)) (PreH19 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH20 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH21 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH22 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_safety_wit_12 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (edge_weight >= 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (0 <= edge)) (PreH11 : (edge < edge_count_pre)) (PreH12 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH13 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH14 : (0 <= neighbor)) (PreH15 : (neighbor < vertex_count_pre)) (PreH16 : (neighbor < 10)) (PreH17 : (0 <= edge_weight)) (PreH18 : (edge_weight <= 1000000000)) (PreH19 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH20 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH21 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH22 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ ((1000000000 - edge_weight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1000000000 - edge_weight )) ”
.

Definition dijkstra_linked_forward_star_safety_wit_13 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (edge_weight >= 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (0 <= edge)) (PreH11 : (edge < edge_count_pre)) (PreH12 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH13 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH14 : (0 <= neighbor)) (PreH15 : (neighbor < vertex_count_pre)) (PreH16 : (neighbor < 10)) (PreH17 : (0 <= edge_weight)) (PreH18 : (edge_weight <= 1000000000)) (PreH19 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH20 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH21 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH22 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition dijkstra_linked_forward_star_safety_wit_14 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance <= (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH4 : (vertex_valid g_low_level_spec source_pre )) (PreH5 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH6 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH7 : (0 <= cur_vertex)) (PreH8 : (cur_vertex < vertex_count_pre)) (PreH9 : (0 <= cur_distance)) (PreH10 : (cur_distance <= 1000000000)) (PreH11 : (0 <= edge)) (PreH12 : (edge < edge_count_pre)) (PreH13 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH14 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH15 : (0 <= neighbor)) (PreH16 : (neighbor < vertex_count_pre)) (PreH17 : (neighbor < 10)) (PreH18 : (0 <= edge_weight)) (PreH19 : (edge_weight <= 1000000000)) (PreH20 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH21 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH22 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH23 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ ((cur_distance + edge_weight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur_distance + edge_weight )) ”
.

Definition dijkstra_linked_forward_star_entail_wit_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist1: (@list Z)) (PreH1 : (dijkstra_init_dist vertex_count_pre source_pre dist1 )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (0 <= edge_count_pre)) (PreH6 : (edge_count_pre <= 200005)) (PreH7 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH8 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH9 : (vector_shape dist0_low_level_spec )) (PreH10 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  (IntArray.full dist_pre 10 dist1 )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  EX (queue_vertices0: (@list Z))  (queue_distances0: (@list Z))  (queue_size0: Z)  (queue_items0: (@list (Z * Z)))  (dist_init: (@list Z)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0)
.

Definition dijkstra_linked_forward_star_entail_wit_2 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (queue_vertices0: (@list Z)) (queue_distances0: (@list Z)) (queue_size0: Z) (queue_items0: (@list (Z * Z))) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 0 (@nil (Z * Z)) )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH7 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH8 : (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init_2 )
|--
  EX (queue_items_initial_after: (@list (Z * Z)))  (queue_vertices: (@list Z))  (queue_distances: (@list Z))  (visited_init: (Z -> Prop))  (dist_init: (@list Z)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (visited_set_empty visited_init ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) ) ” 
  &&  “ (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (queue_vertices0: (@list Z)) (queue_distances0: (@list Z)) (queue_size0: Z) (queue_items0: (@list (Z * Z))) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 0 (@nil (Z * Z)) )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH7 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH8 : (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 )) ,
  TT && emp 
|--
  EX (queue_items_initial_after: (@list (Z * Z)))  (visited_init: (Z -> Prop)) ,
  “ (visited_set_empty visited_init ) ” 
  &&  “ (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_entail_wit_3 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 (0 + 1 ) queue_items_initial_after )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH7 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH8 : (visited_set_empty visited_init )) (PreH9 : (priority_queue_model queue_vertices_2 queue_distances_2 0 (@nil (Z * Z)) )) (PreH10 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (0 + 1 ))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
|--
  EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_items: (@list (Z * Z))) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 (0 + 1 ) queue_items_initial_after )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH7 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH8 : (visited_set_empty visited_init )) (PreH9 : (priority_queue_model queue_vertices_2 queue_distances_2 0 (@nil (Z * Z)) )) (PreH10 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop))  (queue_items: (@list (Z * Z))) ,
  “ ((0 + 1 ) = (Zlength (queue_items))) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_init queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_init queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model vertices1 distances1 (Zlength (queue_items)) queue_items ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_entail_wit_4 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances_2: (@list Z)) (queue_vertices_2: (@list Z)) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) (PreH3 : (retval = 0)) (PreH4 : ((Zlength (queue_items_2)) <> 0)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH8 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH9 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2 )) (PreH10 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_items_2 X_low_level_spec )) (PreH11 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_2)))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur_2 )
|--
  EX (queue_vertices: (@list Z))  (queue_distances: (@list Z))  (queue_items_after: (@list (Z * Z)))  (pop_vertex: Z)  (pop_distance: Z)  (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_items: (@list (Z * Z))) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances_2: (@list Z)) (queue_vertices_2: (@list Z)) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) (PreH3 : (retval = 0)) (PreH4 : ((Zlength (queue_items_2)) <> 0)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH8 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH9 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2 )) (PreH10 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_items_2 X_low_level_spec )) (PreH11 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  TT && emp 
|--
  EX (queue_items_after: (@list (Z * Z)))  (pop_vertex: Z)  (pop_distance: Z)  (visited_cur: (Z -> Prop))  (queue_items: (@list (Z * Z))) ,
  “ ((Zlength (queue_items_2)) = (Zlength (queue_items))) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur_2 queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur_2 queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance ) ” 
  &&  “ (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items)) queue_items ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_entail_wit_5 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (queue_items_after: (@list (Z * Z))) (pop_vertex: Z) (pop_distance: Z) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 ((Zlength (queue_items_2)) - 1 ) queue_items_after )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2 )) (PreH7 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_items_2 X_low_level_spec )) (PreH8 : (priority_queue_pop_result queue_items_2 queue_items_after pop_vertex pop_distance )) (PreH9 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> ((Zlength (queue_items_2)) - 1 ))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur_2 )
|--
  EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_items: (@list (Z * Z))) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (storage_index pop_vertex ) ” 
  &&  “ (0 <= pop_vertex) ” 
  &&  “ (pop_vertex < vertex_count_pre) ” 
  &&  “ (pop_vertex < 10) ” 
  &&  “ (0 <= pop_distance) ” 
  &&  “ (pop_distance <= 1000000000) ” 
  &&  “ (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items pop_vertex pop_distance X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (queue_items_after: (@list (Z * Z))) (pop_vertex: Z) (pop_distance: Z) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 ((Zlength (queue_items_2)) - 1 ) queue_items_after )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2 )) (PreH7 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_items_2 X_low_level_spec )) (PreH8 : (priority_queue_pop_result queue_items_2 queue_items_after pop_vertex pop_distance )) (PreH9 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop))  (queue_items: (@list (Z * Z))) ,
  “ (((Zlength (queue_items_2)) - 1 ) = (Zlength (queue_items))) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur_2 queue_items ) ” 
  &&  “ (storage_index pop_vertex ) ” 
  &&  “ (0 <= pop_vertex) ” 
  &&  “ (pop_vertex < vertex_count_pre) ” 
  &&  “ (pop_vertex < 10) ” 
  &&  “ (0 <= pop_distance) ” 
  &&  “ (pop_distance <= 1000000000) ” 
  &&  “ (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur_2 queue_items pop_vertex pop_distance X_low_level_spec ) ” 
  &&  “ (priority_queue_model vertices1 distances1 (Zlength (queue_items)) queue_items ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_entail_wit_6 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (PreH1 : (cur_distance = (Znth cur_vertex dist_cur 0))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur queue_items_2 )) (PreH7 : (storage_index cur_vertex )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (cur_vertex < 10)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur queue_items_2 cur_vertex cur_distance X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_2)))
|--
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ ((Znth cur_vertex head_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
  ||
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ (0 <= (Znth cur_vertex head_values_low_level_spec 0)) ” 
  &&  “ ((Znth cur_vertex head_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
.

Definition dijkstra_linked_forward_star_entail_wit_7 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances_2: (@list Z)) (queue_vertices_2: (@list Z)) (edge: Z) (dist_edge_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge <> (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_items_2 )) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_items_2 X_low_level_spec )) (PreH15 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge_2 )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_2)))
|--
  EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ ((Znth edge weight_values_low_level_spec 0) = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= (Znth edge to_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) < vertex_count_pre) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) < 10) ” 
  &&  “ (0 <= (Znth edge weight_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge weight_values_low_level_spec 0) <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items ) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances_2: (@list Z)) (queue_vertices_2: (@list Z)) (edge: Z) (dist_edge_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge <> (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_items_2 )) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_items_2 X_low_level_spec )) (PreH15 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  TT && emp 
|--
  EX (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ ((Zlength (queue_items_2)) = (Zlength (queue_items))) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ ((Znth edge weight_values_low_level_spec 0) = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= (Znth edge to_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) < vertex_count_pre) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) < 10) ” 
  &&  “ (0 <= (Znth edge weight_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge weight_values_low_level_spec 0) <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge_2 queue_items ) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge_2 queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items)) queue_items ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_entail_wit_8 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH7 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH15 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH16 : (0 <= neighbor)) (PreH17 : (neighbor < vertex_count_pre)) (PreH18 : (neighbor < 10)) (PreH19 : (0 <= edge_weight)) (PreH20 : (edge_weight <= 1000000000)) (PreH21 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH22 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge queue_items )) (PreH23 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge queue_items X_low_level_spec )) (PreH24 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items)) queue_items )) ,
  (IntArray.full dist_pre 10 (replace_Znth (neighbor) ((cur_distance + edge_weight )) (dist_edge)) )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  EX (queue_vertices: (@list Z))  (queue_distances: (@list Z))  (push_items_after: (@list (Z * Z)))  (dist_after: (@list Z))  (queue_items_before: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (neighbor = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= edge_weight) ” 
  &&  “ (edge_weight <= 1000000000) ” 
  &&  “ ((cur_distance + edge_weight ) = (cur_distance + edge_weight )) ” 
  &&  “ (0 <= (cur_distance + edge_weight )) ” 
  &&  “ ((cur_distance + edge_weight ) <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before ) ” 
  &&  “ (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor (cur_distance + edge_weight ) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec ) ” 
  &&  “ (priority_queue_push_result queue_items_before push_items_after neighbor (cur_distance + edge_weight ) ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_before)))
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH7 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH15 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH16 : (0 <= neighbor)) (PreH17 : (neighbor < vertex_count_pre)) (PreH18 : (neighbor < 10)) (PreH19 : (0 <= edge_weight)) (PreH20 : (edge_weight <= 1000000000)) (PreH21 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH22 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge queue_items )) (PreH23 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge queue_items X_low_level_spec )) (PreH24 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items)) queue_items )) ,
  TT && emp 
|--
  EX (push_items_after: (@list (Z * Z)))  (queue_items_before: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ ((Zlength (queue_items)) = (Zlength (queue_items_before))) ” 
  &&  “ (0 <= (cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) )) ” 
  &&  “ ((cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) ) <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge (replace_Znth ((Znth (edge) (to_values_low_level_spec) (0))) ((cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) )) (dist_edge)) queue_items_before ) ” 
  &&  “ (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge (Znth (edge) (to_values_low_level_spec) (0)) (cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) ) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge (replace_Znth ((Znth (edge) (to_values_low_level_spec) (0))) ((cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) )) (dist_edge)) queue_items_before X_low_level_spec ) ” 
  &&  “ (priority_queue_push_result queue_items_before push_items_after (Znth (edge) (to_values_low_level_spec) (0)) (cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) ) ) ” 
  &&  “ (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_before)) queue_items_before ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_entail_wit_9_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_after: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_items_before: (@list (Z * Z))) (push_items_after: (@list (Z * Z))) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 ((Zlength (queue_items_before)) + 1 ) push_items_after )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (0 <= edge)) (PreH11 : (edge < edge_count_pre)) (PreH12 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH13 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH14 : (0 <= neighbor)) (PreH15 : (neighbor < vertex_count_pre)) (PreH16 : (neighbor < 10)) (PreH17 : (0 <= edge_weight)) (PreH18 : (edge_weight <= 1000000000)) (PreH19 : (candidate = (cur_distance + edge_weight ))) (PreH20 : (0 <= candidate)) (PreH21 : (candidate <= 1000000000)) (PreH22 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH23 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_after queue_items_before )) (PreH24 : (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_after queue_items_before X_low_level_spec )) (PreH25 : (priority_queue_push_result queue_items_before push_items_after neighbor candidate )) (PreH26 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_before)) queue_items_before )) ,
  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> ((Zlength (queue_items_before)) + 1 ))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
|--
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
  ||
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ (0 <= (Znth edge next_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
.

Definition dijkstra_linked_forward_star_entail_wit_9_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge_2: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) >= (Znth neighbor dist_edge_2 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH7 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH15 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH16 : (0 <= neighbor)) (PreH17 : (neighbor < vertex_count_pre)) (PreH18 : (neighbor < 10)) (PreH19 : (0 <= edge_weight)) (PreH20 : (edge_weight <= 1000000000)) (PreH21 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH22 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_items_2 )) (PreH23 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_items_2 X_low_level_spec )) (PreH24 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge_2 )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_2)))
|--
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
  ||
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ (0 <= (Znth edge next_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
.

Definition dijkstra_linked_forward_star_entail_wit_9_3 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge_2: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance > (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH4 : (vertex_valid g_low_level_spec source_pre )) (PreH5 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH6 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH7 : (0 <= cur_vertex)) (PreH8 : (cur_vertex < vertex_count_pre)) (PreH9 : (0 <= cur_distance)) (PreH10 : (cur_distance <= 1000000000)) (PreH11 : (0 <= edge)) (PreH12 : (edge < edge_count_pre)) (PreH13 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH14 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH15 : (0 <= neighbor)) (PreH16 : (neighbor < vertex_count_pre)) (PreH17 : (neighbor < 10)) (PreH18 : (0 <= edge_weight)) (PreH19 : (edge_weight <= 1000000000)) (PreH20 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH21 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_items_2 )) (PreH22 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_items_2 X_low_level_spec )) (PreH23 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge_2 )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_2)))
|--
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
  ||
  (EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (dist_edge: (@list Z))  (queue_items: (@list (Z * Z)))  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_items ) ” 
  &&  “ (0 <= (Znth edge next_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items))))
.

Definition dijkstra_linked_forward_star_entail_wit_10_1 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances_2: (@list Z)) (queue_vertices_2: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items_2: (@list (Z * Z))) (visited_cur_2: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge = (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur_2 cur_vertex visited_edge )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items_2 )) (PreH12 : (edge = (-1))) (PreH13 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items_2 X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_2)))
|--
  EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_items: (@list (Z * Z))) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances_2: (@list Z)) (queue_vertices_2: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items_2: (@list (Z * Z))) (visited_cur_2: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge = (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur_2 cur_vertex visited_edge )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items_2 )) (PreH12 : (edge = (-1))) (PreH13 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items_2 X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop))  (queue_items: (@list (Z * Z))) ,
  “ ((Zlength (queue_items_2)) = (Zlength (queue_items))) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_edge queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items)) queue_items ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_entail_wit_10_2 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (PreH1 : (cur_distance <> (Znth cur_vertex dist_cur_2 0))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2 )) (PreH7 : (storage_index cur_vertex )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (cur_vertex < 10)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_items_2 cur_vertex cur_distance X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  (IntArray.full dist_pre 10 dist_cur_2 )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_2)))
|--
  EX (queue_distances: (@list Z))  (queue_vertices: (@list Z))  (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_items: (@list (Z * Z))) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_vertices_2: (@list Z)) (queue_distances_2: (@list Z)) (queue_items_2: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (PreH1 : (cur_distance <> (Znth cur_vertex dist_cur_2 0))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2 )) (PreH7 : (storage_index cur_vertex )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (cur_vertex < 10)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_items_2 cur_vertex cur_distance X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items_2)) queue_items_2 )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop))  (queue_items: (@list (Z * Z))) ,
  “ ((Zlength (queue_items_2)) = (Zlength (queue_items))) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur_2 queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur_2 queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices_2 queue_distances_2 (Zlength (queue_items)) queue_items ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_return_wit_1 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_items: (@list (Z * Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) (PreH3 : (retval = 1)) (PreH4 : ((Zlength (queue_items)) = 0)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH8 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH9 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH10 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH11 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
|--
  EX (queue_vertices1: (@list Z))  (queue_distances1: (@list Z))  (queue_size1: Z)  (queue_items1: (@list (Z * Z)))  (visited_out: (Z -> Prop))  (dist_out: (@list Z)) ,
  “ (safeExec (graph_state_model (g_low_level_spec) (visited_out) (dist_out)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices1 queue_distances1 queue_size1 queue_items1 ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_out )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size1)
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_items: (@list (Z * Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) (PreH3 : (retval = 1)) (PreH4 : ((Zlength (queue_items)) = 0)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH8 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH9 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH10 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH11 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  TT && emp 
|--
  EX (queue_items1: (@list (Z * Z)))  (visited_out: (Z -> Prop)) ,
  “ (safeExec (graph_state_model (g_low_level_spec) (visited_out) (dist_cur)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items1 ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_partial_solve_wit_1_pure := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (0 <= edge_count_pre)) (PreH5 : (edge_count_pre <= 200005)) (PreH6 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH7 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH8 : (vector_shape dist0_low_level_spec )) (PreH9 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 < vertex_count_pre) ”
) \/
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (queue_size0_low_level_spec <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size0_low_level_spec >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (0 <= edge_count_pre)) (PreH13 : (edge_count_pre <= 200005)) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH15 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (source_pre < vertex_count_pre) ”
).

Definition dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (queue_size0_low_level_spec <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size0_low_level_spec >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (0 <= edge_count_pre)) (PreH13 : (edge_count_pre <= 200005)) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH15 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  “ (0 < vertex_count_pre) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (queue_size0_low_level_spec <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size0_low_level_spec >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (0 <= edge_count_pre)) (PreH13 : (edge_count_pre <= 200005)) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH15 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  “ (vertex_count_pre <= 10) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_3 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (queue_size0_low_level_spec <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size0_low_level_spec >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (0 <= edge_count_pre)) (PreH13 : (edge_count_pre <= 200005)) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH15 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  “ (0 <= source_pre) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_4 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (queue_size0_low_level_spec <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size0_low_level_spec >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (0 <= edge_count_pre)) (PreH13 : (edge_count_pre <= 200005)) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH15 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  “ (source_pre < vertex_count_pre) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_1_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (queue_items0_low_level_spec: (@list (Z * Z))) (queue_size0_low_level_spec: Z) (queue_distances0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (0 <= edge_count_pre)) (PreH5 : (edge_count_pre <= 200005)) (PreH6 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH7 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH8 : (vector_shape dist0_low_level_spec )) (PreH9 : (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
|--
  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= edge_count_pre) ” 
  &&  “ (edge_count_pre <= 200005) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec ) ”
  &&  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec)
.

Definition dijkstra_linked_forward_star_partial_solve_wit_1 := dijkstra_linked_forward_star_partial_solve_wit_1_pure -> dijkstra_linked_forward_star_partial_solve_wit_1_aux.

Definition dijkstra_linked_forward_star_partial_solve_wit_2_pure := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (queue_vertices0: (@list Z)) (queue_distances0: (@list Z)) (queue_size0: Z) (queue_items0: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH6 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH7 : (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0)
|--
  “ (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 ) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_2_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (queue_vertices0: (@list Z)) (queue_distances0: (@list Z)) (queue_size0: Z) (queue_items0: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH6 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH7 : (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0)
|--
  “ (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 ) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices0 queue_distances0 queue_size0 queue_items0 ) ”
  &&  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
.

Definition dijkstra_linked_forward_star_partial_solve_wit_2 := dijkstra_linked_forward_star_partial_solve_wit_2_pure -> dijkstra_linked_forward_star_partial_solve_wit_2_aux.

Definition dijkstra_linked_forward_star_partial_solve_wit_3_pure := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH6 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH7 : (visited_set_empty visited_init )) (PreH8 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH9 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (priority_queue_push_result nil queue_items_initial_after source_pre 0 ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances 0 nil ) ” 
  &&  “ (source_pre < 10) ” 
  &&  “ (0 <= source_pre) ”
) \/
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (0 <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH14 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH15 : (visited_set_empty visited_init )) (PreH16 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH17 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (0 <= source_pre) ” 
  &&  “ (source_pre < 10) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances 0 nil ) ” 
  &&  “ (priority_queue_push_result nil queue_items_initial_after source_pre 0 ) ”
).

Definition dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (0 <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH14 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH15 : (visited_set_empty visited_init )) (PreH16 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH17 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (0 <= source_pre) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (0 <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH14 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH15 : (visited_set_empty visited_init )) (PreH16 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH17 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (source_pre < 10) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_3 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (0 <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH14 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH15 : (visited_set_empty visited_init )) (PreH16 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH17 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (priority_queue_model queue_vertices queue_distances 0 nil ) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_4 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (0 <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH14 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH15 : (visited_set_empty visited_init )) (PreH16 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH17 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (priority_queue_push_result nil queue_items_initial_after source_pre 0 ) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_3_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items_initial_after: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH6 : (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH7 : (visited_set_empty visited_init )) (PreH8 : (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) )) (PreH9 : (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (priority_queue_push_result nil queue_items_initial_after source_pre 0 ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances 0 nil ) ” 
  &&  “ (source_pre < 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (visited_set_empty visited_init ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances 0 (@nil (Z * Z)) ) ” 
  &&  “ (priority_queue_push_result (@nil (Z * Z)) queue_items_initial_after source_pre 0 ) ”
  &&  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> 0)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
.

Definition dijkstra_linked_forward_star_partial_solve_wit_3 := dijkstra_linked_forward_star_partial_solve_wit_3_pure -> dijkstra_linked_forward_star_partial_solve_wit_3_aux.

Definition dijkstra_linked_forward_star_partial_solve_wit_4_pure := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_items: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH6 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH7 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_4_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_items: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH6 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH7 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
.

Definition dijkstra_linked_forward_star_partial_solve_wit_4 := dijkstra_linked_forward_star_partial_solve_wit_4_pure -> dijkstra_linked_forward_star_partial_solve_wit_4_aux.

Definition dijkstra_linked_forward_star_partial_solve_wit_5_pure := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (queue_items_after: (@list (Z * Z))) (pop_vertex: Z) (pop_distance: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH6 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH7 : (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance )) (PreH8 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ” 
  &&  “ (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance ) ” 
  &&  “ ((Zlength (queue_items)) <= 200005) ” 
  &&  “ (0 < (Zlength (queue_items))) ”
) \/
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (queue_items_after: (@list (Z * Z))) (pop_vertex: Z) (pop_distance: Z) (PreH1 : ((Zlength (queue_items)) <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : ((Zlength (queue_items)) >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH14 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH15 : (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance )) (PreH16 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (0 < (Zlength (queue_items))) ” 
  &&  “ ((Zlength (queue_items)) <= 200005) ”
).

Definition dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (queue_items_after: (@list (Z * Z))) (pop_vertex: Z) (pop_distance: Z) (PreH1 : ((Zlength (queue_items)) <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : ((Zlength (queue_items)) >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH14 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH15 : (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance )) (PreH16 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (0 < (Zlength (queue_items))) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (queue_items_after: (@list (Z * Z))) (pop_vertex: Z) (pop_distance: Z) (PreH1 : ((Zlength (queue_items)) <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : ((Zlength (queue_items)) >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH10 : (vertex_valid g_low_level_spec source_pre )) (PreH11 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH13 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH14 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH15 : (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance )) (PreH16 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ ((Zlength (queue_items)) <= 200005) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_5_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (queue_items_after: (@list (Z * Z))) (pop_vertex: Z) (pop_distance: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH6 : (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec )) (PreH7 : (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance )) (PreH8 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ” 
  &&  “ (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance ) ” 
  &&  “ ((Zlength (queue_items)) <= 200005) ” 
  &&  “ (0 < (Zlength (queue_items))) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (dijkstra_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_pop_result queue_items queue_items_after pop_vertex pop_distance ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
.

Definition dijkstra_linked_forward_star_partial_solve_wit_5 := dijkstra_linked_forward_star_partial_solve_wit_5_pure -> dijkstra_linked_forward_star_partial_solve_wit_5_aux.

Definition dijkstra_linked_forward_star_partial_solve_wit_6 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH6 : (storage_index cur_vertex )) (PreH7 : (0 <= cur_vertex)) (PreH8 : (cur_vertex < vertex_count_pre)) (PreH9 : (cur_vertex < 10)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items cur_vertex cur_distance X_low_level_spec )) (PreH13 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (storage_index cur_vertex ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (cur_vertex < 10) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items cur_vertex cur_distance X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((dist_pre + (cur_vertex * sizeof(INT)))) # Int  |-> (Znth cur_vertex dist_cur 0))
  **  (IntArray.missing_i dist_pre cur_vertex 0 10 dist_cur )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_partial_solve_wit_7 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (PreH1 : (cur_distance = (Znth cur_vertex dist_cur 0))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items )) (PreH7 : (storage_index cur_vertex )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (cur_vertex < 10)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items cur_vertex cur_distance X_low_level_spec )) (PreH14 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (cur_distance = (Znth cur_vertex dist_cur 0)) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_items ) ” 
  &&  “ (storage_index cur_vertex ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (cur_vertex < 10) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (dijkstra_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_items cur_vertex cur_distance X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((head_pre + (cur_vertex * sizeof(INT)))) # Int  |-> (Znth cur_vertex head_values_low_level_spec 0))
  **  (IntArray.missing_i head_pre cur_vertex 0 vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_partial_solve_wit_8 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge <> (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH15 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (edge <> (-1)) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items ) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((to_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge to_values_low_level_spec 0))
  **  (IntArray.missing_i to_pre edge 0 edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_partial_solve_wit_9 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (queue_distances: (@list Z)) (queue_vertices: (@list Z)) (edge: Z) (dist_edge: (@list Z)) (queue_items: (@list (Z * Z))) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (PreH1 : (edge <> (-1))) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH11 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH15 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (edge <> (-1)) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items ) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((weight_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge weight_values_low_level_spec 0))
  **  (IntArray.missing_i weight_pre edge 0 edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_partial_solve_wit_10 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance <= (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH4 : (vertex_valid g_low_level_spec source_pre )) (PreH5 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH6 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH7 : (0 <= cur_vertex)) (PreH8 : (cur_vertex < vertex_count_pre)) (PreH9 : (0 <= cur_distance)) (PreH10 : (cur_distance <= 1000000000)) (PreH11 : (0 <= edge)) (PreH12 : (edge < edge_count_pre)) (PreH13 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH14 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH15 : (0 <= neighbor)) (PreH16 : (neighbor < vertex_count_pre)) (PreH17 : (neighbor < 10)) (PreH18 : (0 <= edge_weight)) (PreH19 : (edge_weight <= 1000000000)) (PreH20 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH21 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH22 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH23 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (cur_distance <= (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (neighbor = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= edge_weight) ” 
  &&  “ (edge_weight <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items ) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((dist_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth neighbor dist_edge 0))
  **  (IntArray.missing_i dist_pre neighbor 0 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_partial_solve_wit_11 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH7 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH15 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH16 : (0 <= neighbor)) (PreH17 : (neighbor < vertex_count_pre)) (PreH18 : (neighbor < 10)) (PreH19 : (0 <= edge_weight)) (PreH20 : (edge_weight <= 1000000000)) (PreH21 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH22 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH23 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH24 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0)) ” 
  &&  “ (cur_distance <= (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (neighbor = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= edge_weight) ” 
  &&  “ (edge_weight <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items ) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((dist_pre + (neighbor * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre neighbor 0 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_partial_solve_wit_12_pure := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_items_before: (@list (Z * Z))) (push_items_after: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (0 <= cur_vertex)) (PreH6 : (cur_vertex < vertex_count_pre)) (PreH7 : (0 <= cur_distance)) (PreH8 : (cur_distance <= 1000000000)) (PreH9 : (0 <= edge)) (PreH10 : (edge < edge_count_pre)) (PreH11 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH12 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH13 : (0 <= neighbor)) (PreH14 : (neighbor < vertex_count_pre)) (PreH15 : (neighbor < 10)) (PreH16 : (0 <= edge_weight)) (PreH17 : (edge_weight <= 1000000000)) (PreH18 : (candidate = (cur_distance + edge_weight ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 1000000000)) (PreH21 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH22 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before )) (PreH23 : (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec )) (PreH24 : (priority_queue_push_result queue_items_before push_items_after neighbor candidate )) (PreH25 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_before)))
|--
  “ (0 <= neighbor) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 1000000000) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before ) ” 
  &&  “ (priority_queue_push_result queue_items_before push_items_after neighbor candidate ) ” 
  &&  “ (0 <= (Zlength (queue_items_before))) ”
) \/
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_items_before: (@list (Z * Z))) (push_items_after: (@list (Z * Z))) (PreH1 : ((Zlength (queue_items_before)) <= INT_MAX)) (PreH2 : (candidate <= INT_MAX)) (PreH3 : (edge_weight <= INT_MAX)) (PreH4 : (neighbor <= INT_MAX)) (PreH5 : (edge <= INT_MAX)) (PreH6 : (cur_distance <= INT_MAX)) (PreH7 : (cur_vertex <= INT_MAX)) (PreH8 : (edge_count_pre <= INT_MAX)) (PreH9 : (source_pre <= INT_MAX)) (PreH10 : (vertex_count_pre <= INT_MAX)) (PreH11 : ((Zlength (queue_items_before)) >= INT_MIN)) (PreH12 : (candidate >= INT_MIN)) (PreH13 : (edge_weight >= INT_MIN)) (PreH14 : (neighbor >= INT_MIN)) (PreH15 : (edge >= INT_MIN)) (PreH16 : (cur_distance >= INT_MIN)) (PreH17 : (cur_vertex >= INT_MIN)) (PreH18 : (edge_count_pre >= INT_MIN)) (PreH19 : (source_pre >= INT_MIN)) (PreH20 : (vertex_count_pre >= INT_MIN)) (PreH21 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH22 : (vertex_valid g_low_level_spec source_pre )) (PreH23 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH24 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH25 : (0 <= cur_vertex)) (PreH26 : (cur_vertex < vertex_count_pre)) (PreH27 : (0 <= cur_distance)) (PreH28 : (cur_distance <= 1000000000)) (PreH29 : (0 <= edge)) (PreH30 : (edge < edge_count_pre)) (PreH31 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH32 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH33 : (0 <= neighbor)) (PreH34 : (neighbor < vertex_count_pre)) (PreH35 : (neighbor < 10)) (PreH36 : (0 <= edge_weight)) (PreH37 : (edge_weight <= 1000000000)) (PreH38 : (candidate = (cur_distance + edge_weight ))) (PreH39 : (0 <= candidate)) (PreH40 : (candidate <= 1000000000)) (PreH41 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH42 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before )) (PreH43 : (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec )) (PreH44 : (priority_queue_push_result queue_items_before push_items_after neighbor candidate )) (PreH45 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_before)))
|--
  “ (0 <= (Zlength (queue_items_before))) ”
).

Definition dijkstra_linked_forward_star_partial_solve_wit_12_pure_split_goal_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_items_before: (@list (Z * Z))) (push_items_after: (@list (Z * Z))) (PreH1 : ((Zlength (queue_items_before)) <= INT_MAX)) (PreH2 : (candidate <= INT_MAX)) (PreH3 : (edge_weight <= INT_MAX)) (PreH4 : (neighbor <= INT_MAX)) (PreH5 : (edge <= INT_MAX)) (PreH6 : (cur_distance <= INT_MAX)) (PreH7 : (cur_vertex <= INT_MAX)) (PreH8 : (edge_count_pre <= INT_MAX)) (PreH9 : (source_pre <= INT_MAX)) (PreH10 : (vertex_count_pre <= INT_MAX)) (PreH11 : ((Zlength (queue_items_before)) >= INT_MIN)) (PreH12 : (candidate >= INT_MIN)) (PreH13 : (edge_weight >= INT_MIN)) (PreH14 : (neighbor >= INT_MIN)) (PreH15 : (edge >= INT_MIN)) (PreH16 : (cur_distance >= INT_MIN)) (PreH17 : (cur_vertex >= INT_MIN)) (PreH18 : (edge_count_pre >= INT_MIN)) (PreH19 : (source_pre >= INT_MIN)) (PreH20 : (vertex_count_pre >= INT_MIN)) (PreH21 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH22 : (vertex_valid g_low_level_spec source_pre )) (PreH23 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH24 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH25 : (0 <= cur_vertex)) (PreH26 : (cur_vertex < vertex_count_pre)) (PreH27 : (0 <= cur_distance)) (PreH28 : (cur_distance <= 1000000000)) (PreH29 : (0 <= edge)) (PreH30 : (edge < edge_count_pre)) (PreH31 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH32 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH33 : (0 <= neighbor)) (PreH34 : (neighbor < vertex_count_pre)) (PreH35 : (neighbor < 10)) (PreH36 : (0 <= edge_weight)) (PreH37 : (edge_weight <= 1000000000)) (PreH38 : (candidate = (cur_distance + edge_weight ))) (PreH39 : (0 <= candidate)) (PreH40 : (candidate <= 1000000000)) (PreH41 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH42 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before )) (PreH43 : (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec )) (PreH44 : (priority_queue_push_result queue_items_before push_items_after neighbor candidate )) (PreH45 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  ((( &( "neighbor" ) )) # Int  |-> neighbor)
  **  ((( &( "edge_weight" ) )) # Int  |-> edge_weight)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_before)))
|--
  “ (0 <= (Zlength (queue_items_before))) ”
.

Definition dijkstra_linked_forward_star_partial_solve_wit_12_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_items_before: (@list (Z * Z))) (push_items_after: (@list (Z * Z))) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH4 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH5 : (0 <= cur_vertex)) (PreH6 : (cur_vertex < vertex_count_pre)) (PreH7 : (0 <= cur_distance)) (PreH8 : (cur_distance <= 1000000000)) (PreH9 : (0 <= edge)) (PreH10 : (edge < edge_count_pre)) (PreH11 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH12 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH13 : (0 <= neighbor)) (PreH14 : (neighbor < vertex_count_pre)) (PreH15 : (neighbor < 10)) (PreH16 : (0 <= edge_weight)) (PreH17 : (edge_weight <= 1000000000)) (PreH18 : (candidate = (cur_distance + edge_weight ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 1000000000)) (PreH21 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH22 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before )) (PreH23 : (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec )) (PreH24 : (priority_queue_push_result queue_items_before push_items_after neighbor candidate )) (PreH25 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_before)))
|--
  “ (0 <= neighbor) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 1000000000) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before ) ” 
  &&  “ (priority_queue_push_result queue_items_before push_items_after neighbor candidate ) ” 
  &&  “ (0 <= (Zlength (queue_items_before))) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (neighbor = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= edge_weight) ” 
  &&  “ (edge_weight <= 1000000000) ” 
  &&  “ (candidate = (cur_distance + edge_weight )) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before ) ” 
  &&  “ (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec ) ” 
  &&  “ (priority_queue_push_result queue_items_before push_items_after neighbor candidate ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before ) ”
  &&  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items_before)))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
.

Definition dijkstra_linked_forward_star_partial_solve_wit_12 := dijkstra_linked_forward_star_partial_solve_wit_12_pure -> dijkstra_linked_forward_star_partial_solve_wit_12_aux.

Definition dijkstra_linked_forward_star_partial_solve_wit_13 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_items_before: (@list (Z * Z))) (push_items_after: (@list (Z * Z))) (vertices1: (@list Z)) (distances1: (@list Z)) (PreH1 : (priority_queue_model vertices1 distances1 ((Zlength (queue_items_before)) + 1 ) push_items_after )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH5 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH6 : (0 <= cur_vertex)) (PreH7 : (cur_vertex < vertex_count_pre)) (PreH8 : (0 <= cur_distance)) (PreH9 : (cur_distance <= 1000000000)) (PreH10 : (0 <= edge)) (PreH11 : (edge < edge_count_pre)) (PreH12 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH13 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH14 : (0 <= neighbor)) (PreH15 : (neighbor < vertex_count_pre)) (PreH16 : (neighbor < 10)) (PreH17 : (0 <= edge_weight)) (PreH18 : (edge_weight <= 1000000000)) (PreH19 : (candidate = (cur_distance + edge_weight ))) (PreH20 : (0 <= candidate)) (PreH21 : (candidate <= 1000000000)) (PreH22 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH23 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before )) (PreH24 : (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec )) (PreH25 : (priority_queue_push_result queue_items_before push_items_after neighbor candidate )) (PreH26 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before )) ,
  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> ((Zlength (queue_items_before)) + 1 ))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
|--
  “ (priority_queue_model vertices1 distances1 ((Zlength (queue_items_before)) + 1 ) push_items_after ) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (neighbor = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= edge_weight) ” 
  &&  “ (edge_weight <= 1000000000) ” 
  &&  “ (candidate = (cur_distance + edge_weight )) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_items_before ) ” 
  &&  “ (dijkstra_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_items_before X_low_level_spec ) ” 
  &&  “ (priority_queue_push_result queue_items_before push_items_after neighbor candidate ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items_before)) queue_items_before ) ”
  &&  (((next_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge next_values_low_level_spec 0))
  **  (IntArray.missing_i next_pre edge 0 edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> ((Zlength (queue_items_before)) + 1 ))
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
.

Definition dijkstra_linked_forward_star_partial_solve_wit_14 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) >= (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH7 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH15 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH16 : (0 <= neighbor)) (PreH17 : (neighbor < vertex_count_pre)) (PreH18 : (neighbor < 10)) (PreH19 : (0 <= edge_weight)) (PreH20 : (edge_weight <= 1000000000)) (PreH21 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH22 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH23 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH24 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ ((cur_distance + edge_weight ) >= (Znth neighbor dist_edge 0)) ” 
  &&  “ (cur_distance <= (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (neighbor = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= edge_weight) ” 
  &&  “ (edge_weight <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items ) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((next_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge next_values_low_level_spec 0))
  **  (IntArray.missing_i next_pre edge 0 edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_partial_solve_wit_15 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_vertices: (@list Z)) (queue_distances: (@list Z)) (queue_items: (@list (Z * Z))) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance > (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH4 : (vertex_valid g_low_level_spec source_pre )) (PreH5 : (dijkstra_nonnegative_edges g_low_level_spec )) (PreH6 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH7 : (0 <= cur_vertex)) (PreH8 : (cur_vertex < vertex_count_pre)) (PreH9 : (0 <= cur_distance)) (PreH10 : (cur_distance <= 1000000000)) (PreH11 : (0 <= edge)) (PreH12 : (edge < edge_count_pre)) (PreH13 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH14 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH15 : (0 <= neighbor)) (PreH16 : (neighbor < vertex_count_pre)) (PreH17 : (neighbor < 10)) (PreH18 : (0 <= edge_weight)) (PreH19 : (edge_weight <= 1000000000)) (PreH20 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH21 : (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items )) (PreH22 : (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec )) (PreH23 : (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
|--
  “ (cur_distance > (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (neighbor = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < vertex_count_pre) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (0 <= edge_weight) ” 
  &&  “ (edge_weight <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_items ) ” 
  &&  “ (dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_items X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices queue_distances (Zlength (queue_items)) queue_items ) ”
  &&  (((next_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge next_values_low_level_spec 0))
  **  (IntArray.missing_i next_pre edge 0 edge_count_pre next_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> (Zlength (queue_items)))
.

Definition dijkstra_linked_forward_star_derive_high_level_spec_by_low_level_spec := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (queue_items0_high_level_spec: (@list (Z * Z))) (queue_size0_high_level_spec: Z) (queue_distances0_high_level_spec: (@list Z)) (queue_vertices0_high_level_spec: (@list Z)) (dist0_high_level_spec: (@list Z)) (next_values_high_level_spec: (@list Z)) (weight_values_high_level_spec: (@list Z)) (to_values_high_level_spec: (@list Z)) (head_values_high_level_spec: (@list Z)) (g_high_level_spec: G) ,
  “ (graph_has_size g_high_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_high_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_high_level_spec ) ” 
  &&  “ (dijkstra_no_overflow g_high_level_spec source_pre ) ” 
  &&  “ (0 <= edge_count_pre) ” 
  &&  “ (edge_count_pre <= 200005) ” 
  &&  “ (forward_star_model g_high_level_spec edge_count_pre head_values_high_level_spec to_values_high_level_spec weight_values_high_level_spec next_values_high_level_spec ) ” 
  &&  “ (vector_shape dist0_high_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices0_high_level_spec queue_distances0_high_level_spec queue_size0_high_level_spec queue_items0_high_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_high_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_high_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_high_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_high_level_spec )
  **  (IntArray.full dist_pre 10 dist0_high_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_high_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_high_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_high_level_spec)
|--
EX (g_low_level_spec: G) (head_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (queue_vertices0_low_level_spec: (@list Z)) (queue_distances0_low_level_spec: (@list Z)) (queue_size0_low_level_spec: Z) (queue_items0_low_level_spec: (@list (Z * Z))) (X_low_level_spec: (unit -> (state -> Prop))) ,
  (“ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (dijkstra_nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= edge_count_pre) ” 
  &&  “ (edge_count_pre <= 200005) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (dijkstra_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices0_low_level_spec queue_distances0_low_level_spec queue_size0_low_level_spec queue_items0_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices0_low_level_spec )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances0_low_level_spec )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size0_low_level_spec))
  **
  ((EX queue_vertices1_2 queue_distances1_2 queue_size1_2 queue_items1_2 visited_out dist_out_2,
  “ (safeExec (graph_state_model (g_low_level_spec) (visited_out) (dist_out_2)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (priority_queue_model queue_vertices1_2 queue_distances1_2 queue_size1_2 queue_items1_2 ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_out_2 )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices1_2 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances1_2 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size1_2))
  -*
  (EX queue_vertices1 queue_distances1 queue_size1 queue_items1 dist_out,
  “ (dijkstra_shortest_dist g_high_level_spec source_pre dist_out ) ” 
  &&  “ (priority_queue_model queue_vertices1 queue_distances1 queue_size1 queue_items1 ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_high_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_high_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_high_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_high_level_spec )
  **  (IntArray.full dist_pre 10 dist_out )
  **  (IntArray.full ( &( "priority_queue_vertex" ) ) 200005 queue_vertices1 )
  **  (IntArray.full ( &( "priority_queue_distance" ) ) 200005 queue_distances1 )
  **  ((( &( "priority_queue_size" ) )) # Int  |-> queue_size1)))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_dijkstra_linked_forward_star_init_safety_wit_1 : dijkstra_linked_forward_star_init_safety_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_init_safety_wit_2 : dijkstra_linked_forward_star_init_safety_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_init_safety_wit_3 : dijkstra_linked_forward_star_init_safety_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_init_safety_wit_4 : dijkstra_linked_forward_star_init_safety_wit_4.
Axiom proof_of_dijkstra_linked_forward_star_init_safety_wit_5 : dijkstra_linked_forward_star_init_safety_wit_5.
Axiom proof_of_dijkstra_linked_forward_star_init_entail_wit_1 : dijkstra_linked_forward_star_init_entail_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_init_entail_wit_2 : dijkstra_linked_forward_star_init_entail_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_init_entail_wit_3 : dijkstra_linked_forward_star_init_entail_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_init_return_wit_1 : dijkstra_linked_forward_star_init_return_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_init_partial_solve_wit_1 : dijkstra_linked_forward_star_init_partial_solve_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_init_partial_solve_wit_2 : dijkstra_linked_forward_star_init_partial_solve_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_1 : dijkstra_linked_forward_star_safety_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_2 : dijkstra_linked_forward_star_safety_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_3 : dijkstra_linked_forward_star_safety_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_4 : dijkstra_linked_forward_star_safety_wit_4.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_5 : dijkstra_linked_forward_star_safety_wit_5.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_6 : dijkstra_linked_forward_star_safety_wit_6.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_7 : dijkstra_linked_forward_star_safety_wit_7.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_8 : dijkstra_linked_forward_star_safety_wit_8.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_9 : dijkstra_linked_forward_star_safety_wit_9.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_10 : dijkstra_linked_forward_star_safety_wit_10.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_11 : dijkstra_linked_forward_star_safety_wit_11.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_12 : dijkstra_linked_forward_star_safety_wit_12.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_13 : dijkstra_linked_forward_star_safety_wit_13.
Axiom proof_of_dijkstra_linked_forward_star_safety_wit_14 : dijkstra_linked_forward_star_safety_wit_14.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_1 : dijkstra_linked_forward_star_entail_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_2 : dijkstra_linked_forward_star_entail_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_3 : dijkstra_linked_forward_star_entail_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_4 : dijkstra_linked_forward_star_entail_wit_4.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_5 : dijkstra_linked_forward_star_entail_wit_5.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_6 : dijkstra_linked_forward_star_entail_wit_6.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_7 : dijkstra_linked_forward_star_entail_wit_7.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_8 : dijkstra_linked_forward_star_entail_wit_8.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_9_1 : dijkstra_linked_forward_star_entail_wit_9_1.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_9_2 : dijkstra_linked_forward_star_entail_wit_9_2.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_9_3 : dijkstra_linked_forward_star_entail_wit_9_3.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_10_1 : dijkstra_linked_forward_star_entail_wit_10_1.
Axiom proof_of_dijkstra_linked_forward_star_entail_wit_10_2 : dijkstra_linked_forward_star_entail_wit_10_2.
Axiom proof_of_dijkstra_linked_forward_star_return_wit_1 : dijkstra_linked_forward_star_return_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure : dijkstra_linked_forward_star_partial_solve_wit_1_pure.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_1 : dijkstra_linked_forward_star_partial_solve_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_2_pure : dijkstra_linked_forward_star_partial_solve_wit_2_pure.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_2 : dijkstra_linked_forward_star_partial_solve_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure : dijkstra_linked_forward_star_partial_solve_wit_3_pure.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_3 : dijkstra_linked_forward_star_partial_solve_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_4_pure : dijkstra_linked_forward_star_partial_solve_wit_4_pure.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_4 : dijkstra_linked_forward_star_partial_solve_wit_4.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_5_pure : dijkstra_linked_forward_star_partial_solve_wit_5_pure.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_5 : dijkstra_linked_forward_star_partial_solve_wit_5.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_6 : dijkstra_linked_forward_star_partial_solve_wit_6.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_7 : dijkstra_linked_forward_star_partial_solve_wit_7.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_8 : dijkstra_linked_forward_star_partial_solve_wit_8.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_9 : dijkstra_linked_forward_star_partial_solve_wit_9.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_10 : dijkstra_linked_forward_star_partial_solve_wit_10.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_11 : dijkstra_linked_forward_star_partial_solve_wit_11.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_12_pure : dijkstra_linked_forward_star_partial_solve_wit_12_pure.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_12 : dijkstra_linked_forward_star_partial_solve_wit_12.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_13 : dijkstra_linked_forward_star_partial_solve_wit_13.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_14 : dijkstra_linked_forward_star_partial_solve_wit_14.
Axiom proof_of_dijkstra_linked_forward_star_partial_solve_wit_15 : dijkstra_linked_forward_star_partial_solve_wit_15.
Axiom proof_of_dijkstra_linked_forward_star_derive_high_level_spec_by_low_level_spec : dijkstra_linked_forward_star_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
