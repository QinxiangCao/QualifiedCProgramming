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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib.
Require Import Algorithms.Dijkstra.Dijkstra.
From GraphLib Require Import Zweight.
Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_decrease_key_lib.
Import DijkstraGraph.
Import DijkstraLinkedForwardStar.
Import DijkstraDecreaseKey.
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

(*----- Function dijkstra_linked_forward_star_decrease_key -----*)

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist1: (@list Z)) (PreH1 : (dijkstra_init_dist vertex_count_pre source_pre dist1 )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (0 <= edge_count_pre)) (PreH9 : (edge_count_pre <= 100000)) (PreH10 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH11 : (vector_shape dist0_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "queue_pos" ) ) 10 )
  **  (IntArray.undef_full ( &( "queue_data" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_key" ) ) 100000 )
  **  (IntArray.full dist_pre 10 dist1 )
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
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 10)) (PreH3 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH4 : (vertex_valid g_low_level_spec source_pre )) (PreH5 : (nonnegative_edges g_low_level_spec )) (PreH6 : (0 < heap_capacity)) (PreH7 : (100000 <= heap_capacity)) (PreH8 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH9 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH10 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH11 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) i 10 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_3 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) i 10 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_4 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) i 10 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_5 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full ( &( "queue_pos" ) ) (i + 1 ) (app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) (i + 1 ) 10 )
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_6 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (nonnegative_edges g_low_level_spec )) (PreH4 : (0 < heap_capacity)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH8 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH9 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "queue_size" ) )) # Int  |->_)
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
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) 10 (repeat_Z ((-1)) (10)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_7 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_8 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_9 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_10 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_11 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_12 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_map: partial_map) (queue_size: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH9 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH10 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_13 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_size: Z) (queue_map: partial_map) (PreH1 : (0 < queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH9 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH10 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_14 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_size: Z) (queue_map: partial_map) (PreH1 : (0 < queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH9 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH10 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_15 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_size: Z) (queue_map: partial_map) (PreH1 : (0 < queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH9 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH10 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_16 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_size: Z) (queue_map: partial_map) (PreH1 : (0 < queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH9 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH10 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_17 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH13 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_18 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH13 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH14 : (edge = (-1))) (PreH15 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH16 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_19 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH13 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH14 : (edge = (-1))) (PreH15 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH16 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_20 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH13 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_21 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge <> (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH15 : (edge = (-1))) (PreH16 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_22 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge = (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH18 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  ((( &( "cur_vertex" ) )) # Int  |-> cur_vertex)
  **  ((( &( "cur_distance" ) )) # Int  |-> cur_distance)
  **  ((( &( "edge" ) )) # Int  |-> edge)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_23 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (0 <= cur_vertex)) (PreH9 : (cur_vertex < vertex_count_pre)) (PreH10 : (0 <= cur_distance)) (PreH11 : (cur_distance <= 1000000000)) (PreH12 : (0 <= edge)) (PreH13 : (edge < edge_count_pre)) (PreH14 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH15 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH16 : (0 <= neighbor)) (PreH17 : (neighbor < vertex_count_pre)) (PreH18 : (neighbor < 10)) (PreH19 : (0 <= edge_weight)) (PreH20 : (edge_weight <= 1000000000)) (PreH21 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH22 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH23 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH24 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_24 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (edge_weight < 0)) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH23 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH24 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH25 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ False ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_25 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (edge_weight >= 0)) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH23 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH24 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH25 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ ((1000000000 - edge_weight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1000000000 - edge_weight )) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_26 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (edge_weight >= 0)) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH23 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH24 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH25 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_27 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance <= (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (0 <= queue_size)) (PreH4 : (queue_size <= 100000)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (0 <= cur_distance)) (PreH13 : (cur_distance <= 1000000000)) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH17 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH18 : (0 <= neighbor)) (PreH19 : (neighbor < vertex_count_pre)) (PreH20 : (neighbor < 10)) (PreH21 : (0 <= edge_weight)) (PreH22 : (edge_weight <= 1000000000)) (PreH23 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH24 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH25 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH26 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ ((cur_distance + edge_weight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur_distance + edge_weight )) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_28 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (queue_size < heap_capacity)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (candidate = (cur_distance + edge_weight ))) (PreH23 : (0 <= candidate)) (PreH24 : (candidate <= 1000000000)) (PreH25 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH26 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before )) (PreH27 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec )) (PreH28 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH29 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH30 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_29 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (queue_size < heap_capacity)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (candidate = (cur_distance + edge_weight ))) (PreH23 : (0 <= candidate)) (PreH24 : (candidate <= 1000000000)) (PreH25 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH26 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before )) (PreH27 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec )) (PreH28 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH29 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH30 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_30 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (queue_size < heap_capacity)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (candidate = (cur_distance + edge_weight ))) (PreH23 : (0 <= candidate)) (PreH24 : (candidate <= 1000000000)) (PreH25 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH26 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before )) (PreH27 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec )) (PreH28 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH29 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH30 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dijkstra_linked_forward_star_decrease_key_safety_wit_31 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (queue_size < heap_capacity)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (candidate = (cur_distance + edge_weight ))) (PreH23 : (0 <= candidate)) (PreH24 : (candidate <= 1000000000)) (PreH25 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH26 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before )) (PreH27 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec )) (PreH28 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH29 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH30 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_1 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist1: (@list Z)) (PreH1 : (dijkstra_init_dist vertex_count_pre source_pre dist1 )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (0 <= edge_count_pre)) (PreH9 : (edge_count_pre <= 100000)) (PreH10 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH11 : (vector_shape dist0_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.undef_full ( &( "queue_pos" ) ) 10 )
  **  (IntArray.undef_full ( &( "queue_data" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_key" ) ) 100000 )
  **  (IntArray.full dist_pre 10 dist1 )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
|--
  EX (dist_init: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) 0 (repeat_Z ((-1)) (0)) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) 0 10 )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist1: (@list Z)) (PreH1 : (dijkstra_init_dist vertex_count_pre source_pre dist1 )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (0 <= edge_count_pre)) (PreH9 : (edge_count_pre <= 100000)) (PreH10 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH11 : (vector_shape dist0_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.undef_full ( &( "queue_data" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_key" ) ) 100000 )
|--
  “ ((repeat_Z ((-1)) (0)) = (@nil Z)) ”
  &&  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_1_split_goal_1 := 
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist1: (@list Z)) (PreH1 : (dijkstra_init_dist vertex_count_pre source_pre dist1 )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (0 <= edge_count_pre)) (PreH9 : (edge_count_pre <= 100000)) (PreH10 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH11 : (vector_shape dist0_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.undef_full ( &( "queue_data" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_key" ) ) 100000 )
|--
  “ ((repeat_Z ((-1)) (0)) = (@nil Z)) ”
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_1_split_goal_spatial := 
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist1: (@list Z)) (PreH1 : (dijkstra_init_dist vertex_count_pre source_pre dist1 )) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (0 <= edge_count_pre)) (PreH9 : (edge_count_pre <= 100000)) (PreH10 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH11 : (vector_shape dist0_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.undef_full ( &( "queue_data" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_key" ) ) 100000 )
|--
  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_2 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full ( &( "queue_pos" ) ) (i + 1 ) (app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) (i + 1 ) 10 )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init_2 )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
|--
  EX (dist_init: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 10) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) (i + 1 ) (repeat_Z ((-1)) ((i + 1 ))) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) (i + 1 ) 10 )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  TT && emp 
|--
  “ ((app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) = (repeat_Z ((-1)) ((i + 1 )))) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_2_split_goal_1 := 
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) = (repeat_Z ((-1)) ((i + 1 ))))
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_3 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (i: Z) (PreH1 : (i >= 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init_2 )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) i 10 )
|--
  EX (dist_init: (@list Z)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) 10 (repeat_Z ((-1)) (10)) )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (i: Z) (PreH1 : (i >= 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
|--
  (IntArray.full ( &( "queue_pos" ) ) 10 (repeat_Z ((-1)) (10)) )
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_3_split_goal_spatial := 
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (i: Z) (PreH1 : (i >= 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
|--
  (IntArray.full ( &( "queue_pos" ) ) 10 (repeat_Z ((-1)) (10)) )
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_4 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (nonnegative_edges g_low_level_spec )) (PreH4 : (0 < heap_capacity)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH8 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH9 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init_2 )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) 10 (repeat_Z ((-1)) (10)) )
|--
  EX (queue_map_initial_after: partial_map)  (queue_map_empty: partial_map)  (visited_init: (Z -> Prop))  (dist_init: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (visited_set_empty visited_init ) ” 
  &&  “ (queue_map_empty = partial_map_empty) ” 
  &&  “ (partial_map_absent queue_map_empty source_pre ) ” 
  &&  “ (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init_2: (@list Z)) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (nonnegative_edges g_low_level_spec )) (PreH4 : (0 < heap_capacity)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 )) (PreH8 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH9 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) 10 (repeat_Z ((-1)) (10)) )
|--
  EX (queue_map_initial_after: partial_map)  (visited_init: (Z -> Prop)) ,
  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init_2 ) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (visited_set_empty visited_init ) ” 
  &&  “ (partial_map_absent partial_map_empty source_pre ) ” 
  &&  “ (dk_map_queue_push_result partial_map_empty queue_map_initial_after source_pre 0 ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 partial_map_empty 0 )
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_5 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 (partial_map_add (queue_map_empty) (source_pre) (0)) (queue_size + 1 ) )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
|--
  EX (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_map: partial_map) ,
  “ (0 <= (queue_size + 1 )) ” 
  &&  “ ((queue_size + 1 ) <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map (queue_size + 1 ) )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop)) ,
  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= 100000) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_init (partial_map_add (partial_map_empty) (source_pre) (0)) ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_init (partial_map_add (partial_map_empty) (source_pre) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_6 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_map_2: partial_map) (queue_size: Z) (PreH1 : (queue_size <> 0)) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_map_2 )) (PreH10 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_map_2 X_low_level_spec )) (PreH11 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur_2 )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_2 queue_size )
|--
  EX (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_map: partial_map) ,
  “ (0 < queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_map_2: partial_map) (queue_size: Z) (PreH1 : (queue_size <> 0)) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_map_2 )) (PreH10 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_map_2 X_low_level_spec )) (PreH11 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop)) ,
  “ (0 < queue_size) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur_2 queue_map_2 ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur_2 queue_map_2 X_low_level_spec ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_7 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_size: Z) (queue_map_2: partial_map) (data_out_callee_v: Z) (popped: (Z * Z)) (key_out_callee_v: Z) (PreH1 : (key_out_callee_v = (item_key (popped)))) (PreH2 : (data_out_callee_v = (item_data (popped)))) (PreH3 : (partial_map_minimum queue_map_2 popped )) (PreH4 : (0 < queue_size)) (PreH5 : (queue_size <= 100000)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH9 : (vertex_valid g_low_level_spec source_pre )) (PreH10 : (nonnegative_edges g_low_level_spec )) (PreH11 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_map_2 )) (PreH12 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_map_2 X_low_level_spec )) (PreH13 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 (partial_map_remove (queue_map_2) ((item_data (popped)))) (queue_size - 1 ) )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur_2 )
|--
  EX (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_map_before: partial_map) ,
  “ (0 <= (queue_size - 1 )) ” 
  &&  “ ((queue_size - 1 ) < 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map_before ) ” 
  &&  “ (storage_index data_out_callee_v ) ” 
  &&  “ (0 <= data_out_callee_v) ” 
  &&  “ (data_out_callee_v < vertex_count_pre) ” 
  &&  “ (data_out_callee_v < 10) ” 
  &&  “ (0 <= key_out_callee_v) ” 
  &&  “ (key_out_callee_v <= 1000000000) ” 
  &&  “ (dk_map_queue_pop_result queue_map_before queue_map data_out_callee_v key_out_callee_v ) ” 
  &&  “ (dijkstra_dk_map_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map data_out_callee_v key_out_callee_v X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map (queue_size - 1 ) )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur_2: (@list Z)) (queue_size: Z) (queue_map_2: partial_map) (data_out_callee_v: Z) (popped: (Z * Z)) (key_out_callee_v: Z) (PreH1 : (key_out_callee_v = (item_key (popped)))) (PreH2 : (data_out_callee_v = (item_data (popped)))) (PreH3 : (partial_map_minimum queue_map_2 popped )) (PreH4 : (0 < queue_size)) (PreH5 : (queue_size <= 100000)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH9 : (vertex_valid g_low_level_spec source_pre )) (PreH10 : (nonnegative_edges g_low_level_spec )) (PreH11 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_map_2 )) (PreH12 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur_2 queue_map_2 X_low_level_spec )) (PreH13 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop))  (queue_map_before: partial_map) ,
  “ (0 <= (queue_size - 1 )) ” 
  &&  “ ((queue_size - 1 ) < 100000) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur_2 queue_map_before ) ” 
  &&  “ (storage_index (item_data (popped)) ) ” 
  &&  “ (0 <= (item_data (popped))) ” 
  &&  “ ((item_data (popped)) < vertex_count_pre) ” 
  &&  “ ((item_data (popped)) < 10) ” 
  &&  “ (0 <= (item_key (popped))) ” 
  &&  “ ((item_key (popped)) <= 1000000000) ” 
  &&  “ (dk_map_queue_pop_result queue_map_before (partial_map_remove (queue_map_2) ((item_data (popped)))) (item_data (popped)) (item_key (popped)) ) ” 
  &&  “ (dijkstra_dk_map_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur_2 (partial_map_remove (queue_map_2) ((item_data (popped)))) (item_data (popped)) (item_key (popped)) X_low_level_spec ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_8 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (dist_cur: (@list Z)) (queue_map_before: partial_map) (queue_map_2: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur_2 dist_cur queue_map_before )) (PreH9 : (storage_index cur_vertex )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (cur_vertex < 10)) (PreH13 : (0 <= cur_distance)) (PreH14 : (cur_distance <= 1000000000)) (PreH15 : (dk_map_queue_pop_result queue_map_before queue_map_2 cur_vertex cur_distance )) (PreH16 : (dijkstra_dk_map_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur_2 dist_cur queue_map_2 cur_vertex cur_distance X_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_2 queue_size )
|--
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ ((Znth cur_vertex head_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size ))
  ||
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ (0 <= (Znth cur_vertex head_values_low_level_spec 0)) ” 
  &&  “ ((Znth cur_vertex head_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth cur_vertex head_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size ))
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_9 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge_2: (@list Z)) (queue_map_2: partial_map) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge <> (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_map_2 )) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_map_2 X_low_level_spec )) (PreH18 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge_2 )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_2 queue_size )
|--
  EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge_2: (@list Z)) (queue_map_2: partial_map) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge <> (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_map_2 )) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_map_2 X_low_level_spec )) (PreH18 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ ((Znth edge to_values_low_level_spec 0) = (Znth (edge) (to_values_low_level_spec) (0))) ” 
  &&  “ ((Znth edge weight_values_low_level_spec 0) = (Znth (edge) (weight_values_low_level_spec) (0))) ” 
  &&  “ (0 <= (Znth edge to_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) < vertex_count_pre) ” 
  &&  “ ((Znth edge to_values_low_level_spec 0) < 10) ” 
  &&  “ (0 <= (Znth edge weight_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge weight_values_low_level_spec 0) <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge_2 queue_map_2 ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge_2 queue_map_2 X_low_level_spec ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_10 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (0 <= queue_size)) (PreH5 : (queue_size <= 100000)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH9 : (vertex_valid g_low_level_spec source_pre )) (PreH10 : (nonnegative_edges g_low_level_spec )) (PreH11 : (0 <= cur_vertex)) (PreH12 : (cur_vertex < vertex_count_pre)) (PreH13 : (0 <= cur_distance)) (PreH14 : (cur_distance <= 1000000000)) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH18 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH19 : (0 <= neighbor)) (PreH20 : (neighbor < vertex_count_pre)) (PreH21 : (neighbor < 10)) (PreH22 : (0 <= edge_weight)) (PreH23 : (edge_weight <= 1000000000)) (PreH24 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH25 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge queue_map )) (PreH26 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge queue_map X_low_level_spec )) (PreH27 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full dist_pre 10 (replace_Znth (neighbor) ((cur_distance + edge_weight )) (dist_edge)) )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  EX (queue_map_after: partial_map)  (queue_size_after: Z)  (dist_after: (@list Z))  (queue_map_before: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (queue_size < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before ) ” 
  &&  “ (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor (cur_distance + edge_weight ) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec ) ” 
  &&  “ (partial_map_update_or_add_pre queue_map_before neighbor (cur_distance + edge_weight ) ) ” 
  &&  “ (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor (cur_distance + edge_weight ) ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (0 <= queue_size)) (PreH5 : (queue_size <= 100000)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH9 : (vertex_valid g_low_level_spec source_pre )) (PreH10 : (nonnegative_edges g_low_level_spec )) (PreH11 : (0 <= cur_vertex)) (PreH12 : (cur_vertex < vertex_count_pre)) (PreH13 : (0 <= cur_distance)) (PreH14 : (cur_distance <= 1000000000)) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH18 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH19 : (0 <= neighbor)) (PreH20 : (neighbor < vertex_count_pre)) (PreH21 : (neighbor < 10)) (PreH22 : (0 <= edge_weight)) (PreH23 : (edge_weight <= 1000000000)) (PreH24 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH25 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge queue_map )) (PreH26 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge queue_map X_low_level_spec )) (PreH27 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  TT && emp 
|--
  EX (queue_map_after: partial_map)  (queue_size_after: Z)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (queue_size < 100000) ” 
  &&  “ (queue_size < heap_capacity) ” 
  &&  “ (0 <= (cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) )) ” 
  &&  “ ((cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) ) <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge (replace_Znth ((Znth (edge) (to_values_low_level_spec) (0))) ((cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) )) (dist_edge)) queue_map ) ” 
  &&  “ (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge (Znth (edge) (to_values_low_level_spec) (0)) (cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) ) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge (replace_Znth ((Znth (edge) (to_values_low_level_spec) (0))) ((cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) )) (dist_edge)) queue_map X_low_level_spec ) ” 
  &&  “ (partial_map_update_or_add_pre queue_map (Znth (edge) (to_values_low_level_spec) (0)) (cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) ) ) ” 
  &&  “ (dk_map_queue_update_or_push_result queue_map queue_map_after queue_size queue_size_after (Znth (edge) (to_values_low_level_spec) (0)) (cur_distance + (Znth (edge) (weight_values_low_level_spec) (0)) ) ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_11_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (n_after: Z) (PreH1 : (partial_map_update_or_add_size queue_map_before queue_size n_after neighbor candidate )) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size < 100000)) (PreH4 : (queue_size < heap_capacity)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (0 <= cur_distance)) (PreH13 : (cur_distance <= 1000000000)) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH17 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH18 : (0 <= neighbor)) (PreH19 : (neighbor < vertex_count_pre)) (PreH20 : (neighbor < 10)) (PreH21 : (0 <= edge_weight)) (PreH22 : (edge_weight <= 1000000000)) (PreH23 : (candidate = (cur_distance + edge_weight ))) (PreH24 : (0 <= candidate)) (PreH25 : (candidate <= 1000000000)) (PreH26 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH27 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_after queue_map_before )) (PreH28 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_after queue_map_before X_low_level_spec )) (PreH29 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH30 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH31 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 (partial_map_update_or_add (queue_map_before) (neighbor) (candidate)) n_after )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
|--
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= n_after) ” 
  &&  “ (n_after <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map n_after ))
  ||
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= n_after) ” 
  &&  “ (n_after <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ (0 <= (Znth edge next_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map n_after ))
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_11_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge_2: (@list Z)) (queue_map_2: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) >= (Znth neighbor dist_edge_2 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (0 <= queue_size)) (PreH5 : (queue_size <= 100000)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH9 : (vertex_valid g_low_level_spec source_pre )) (PreH10 : (nonnegative_edges g_low_level_spec )) (PreH11 : (0 <= cur_vertex)) (PreH12 : (cur_vertex < vertex_count_pre)) (PreH13 : (0 <= cur_distance)) (PreH14 : (cur_distance <= 1000000000)) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH18 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH19 : (0 <= neighbor)) (PreH20 : (neighbor < vertex_count_pre)) (PreH21 : (neighbor < 10)) (PreH22 : (0 <= edge_weight)) (PreH23 : (edge_weight <= 1000000000)) (PreH24 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH25 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_map_2 )) (PreH26 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_map_2 X_low_level_spec )) (PreH27 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge_2 )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_2 queue_size )
|--
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size ))
  ||
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ (0 <= (Znth edge next_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size ))
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_11_3 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur_2: (Z -> Prop)) (visited_edge_2: (Z -> Prop)) (dist_edge_2: (@list Z)) (queue_map_2: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance > (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (0 <= queue_size)) (PreH4 : (queue_size <= 100000)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (0 <= cur_distance)) (PreH13 : (cur_distance <= 1000000000)) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH17 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH18 : (0 <= neighbor)) (PreH19 : (neighbor < vertex_count_pre)) (PreH20 : (neighbor < 10)) (PreH21 : (0 <= edge_weight)) (PreH22 : (edge_weight <= 1000000000)) (PreH23 : (visited_set_add visited_cur_2 cur_vertex visited_edge_2 )) (PreH24 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge dist_edge_2 queue_map_2 )) (PreH25 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge_2 dist_edge_2 queue_map_2 X_low_level_spec )) (PreH26 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge_2 )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_2 queue_size )
|--
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) = (-1)) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size ))
  ||
  (EX (dist_edge: (@list Z))  (queue_map: partial_map)  (visited_cur: (Z -> Prop))  (visited_edge: (Z -> Prop)) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) dist_edge queue_map ) ” 
  &&  “ (0 <= (Znth edge next_values_low_level_spec 0)) ” 
  &&  “ ((Znth edge next_values_low_level_spec 0) < edge_count_pre) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance (Znth edge next_values_low_level_spec 0) head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size ))
.

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_12 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map_2: partial_map) (visited_cur_2: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge = (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur_2 cur_vertex visited_edge )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map_2 )) (PreH15 : (edge = (-1))) (PreH16 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map_2 X_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_2 queue_size )
|--
  EX (visited_cur: (Z -> Prop))  (dist_cur: (@list Z))  (queue_map: partial_map) ,
  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map_2: partial_map) (visited_cur_2: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge = (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur_2 cur_vertex visited_edge )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map_2 )) (PreH15 : (edge = (-1))) (PreH16 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map_2 X_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  TT && emp 
|--
  EX (visited_cur: (Z -> Prop)) ,
  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_edge queue_map_2 ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_edge queue_map_2 X_low_level_spec ) ”
  &&  emp
).

Definition dijkstra_linked_forward_star_decrease_key_entail_wit_13 := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_map: partial_map) (queue_size: Z) (PreH1 : (queue_size = 0)) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH10 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH11 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  EX (visited_out: (Z -> Prop))  (dist_out: (@list Z))  (queue_map_out: partial_map) ,
  “ (queue_size = 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_out dist_out queue_map_out ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_out dist_out queue_map_out X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (safeExec (graph_state_model (g_low_level_spec) (visited_out) (dist_out)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_out )
  **  (IntArray.undef_full ( &( "queue_key" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_data" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_pos" ) ) 10 )
) \/
(
forall (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_map: partial_map) (queue_size: Z) (PreH1 : (queue_size = 0)) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH10 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH11 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  EX (visited_out: (Z -> Prop))  (queue_map_out: partial_map) ,
  “ (queue_size = 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_out dist_cur queue_map_out ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_out dist_cur queue_map_out X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ” 
  &&  “ (safeExec (graph_state_model (g_low_level_spec) (visited_out) (dist_cur)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.undef_full ( &( "queue_key" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_data" ) ) 100000 )
  **  (IntArray.undef_full ( &( "queue_pos" ) ) 10 )
).

Definition dijkstra_linked_forward_star_decrease_key_return_wit_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_out_2: (Z -> Prop)) (dist_out_2: (@list Z)) (queue_map_out: partial_map) (queue_size: Z) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_out_2 dist_out_2 queue_map_out )) (PreH8 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_out_2 dist_out_2 queue_map_out X_low_level_spec )) (PreH9 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) (PreH10 : (safeExec (graph_state_model (g_low_level_spec) (visited_out_2) (dist_out_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_out_2 )
|--
  EX (visited_out: (Z -> Prop))  (dist_out: (@list Z)) ,
  “ (safeExec (graph_state_model (g_low_level_spec) (visited_out) (dist_out)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_out )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (nonnegative_edges g_low_level_spec )) (PreH4 : (0 < heap_capacity)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (0 <= edge_count_pre)) (PreH8 : (edge_count_pre <= 100000)) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (vector_shape dist0_low_level_spec )) (PreH11 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
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
|--
  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 < vertex_count_pre) ”
) \/
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (edge_count_pre <= INT_MAX)) (PreH2 : (source_pre <= INT_MAX)) (PreH3 : (vertex_count_pre <= INT_MAX)) (PreH4 : (edge_count_pre >= INT_MIN)) (PreH5 : (source_pre >= INT_MIN)) (PreH6 : (vertex_count_pre >= INT_MIN)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 < heap_capacity)) (PreH11 : (100000 <= heap_capacity)) (PreH12 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH13 : (0 <= edge_count_pre)) (PreH14 : (edge_count_pre <= 100000)) (PreH15 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
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
|--
  “ (0 < vertex_count_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (source_pre < vertex_count_pre) ”
).

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (edge_count_pre <= INT_MAX)) (PreH2 : (source_pre <= INT_MAX)) (PreH3 : (vertex_count_pre <= INT_MAX)) (PreH4 : (edge_count_pre >= INT_MIN)) (PreH5 : (source_pre >= INT_MIN)) (PreH6 : (vertex_count_pre >= INT_MIN)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 < heap_capacity)) (PreH11 : (100000 <= heap_capacity)) (PreH12 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH13 : (0 <= edge_count_pre)) (PreH14 : (edge_count_pre <= 100000)) (PreH15 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
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
|--
  “ (0 < vertex_count_pre) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (edge_count_pre <= INT_MAX)) (PreH2 : (source_pre <= INT_MAX)) (PreH3 : (vertex_count_pre <= INT_MAX)) (PreH4 : (edge_count_pre >= INT_MIN)) (PreH5 : (source_pre >= INT_MIN)) (PreH6 : (vertex_count_pre >= INT_MIN)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 < heap_capacity)) (PreH11 : (100000 <= heap_capacity)) (PreH12 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH13 : (0 <= edge_count_pre)) (PreH14 : (edge_count_pre <= 100000)) (PreH15 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
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
|--
  “ (vertex_count_pre <= 10) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_3 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (edge_count_pre <= INT_MAX)) (PreH2 : (source_pre <= INT_MAX)) (PreH3 : (vertex_count_pre <= INT_MAX)) (PreH4 : (edge_count_pre >= INT_MIN)) (PreH5 : (source_pre >= INT_MIN)) (PreH6 : (vertex_count_pre >= INT_MIN)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 < heap_capacity)) (PreH11 : (100000 <= heap_capacity)) (PreH12 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH13 : (0 <= edge_count_pre)) (PreH14 : (edge_count_pre <= 100000)) (PreH15 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
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
|--
  “ (0 <= source_pre) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_4 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (edge_count_pre <= INT_MAX)) (PreH2 : (source_pre <= INT_MAX)) (PreH3 : (vertex_count_pre <= INT_MAX)) (PreH4 : (edge_count_pre >= INT_MIN)) (PreH5 : (source_pre >= INT_MIN)) (PreH6 : (vertex_count_pre >= INT_MIN)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 < heap_capacity)) (PreH11 : (100000 <= heap_capacity)) (PreH12 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH13 : (0 <= edge_count_pre)) (PreH14 : (edge_count_pre <= 100000)) (PreH15 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH16 : (vector_shape dist0_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
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
|--
  “ (source_pre < vertex_count_pre) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (PreH1 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH2 : (vertex_valid g_low_level_spec source_pre )) (PreH3 : (nonnegative_edges g_low_level_spec )) (PreH4 : (0 < heap_capacity)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (0 <= edge_count_pre)) (PreH8 : (edge_count_pre <= 100000)) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (vector_shape dist0_low_level_spec )) (PreH11 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec )
|--
  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (source_pre < vertex_count_pre) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (vertex_count_pre <= 10) ” 
  &&  “ (0 < vertex_count_pre) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (0 <= edge_count_pre) ” 
  &&  “ (edge_count_pre <= 100000) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full dist_pre 10 dist0_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1 := dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure -> dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_aux.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (dist_init: (@list Z)) (i: Z) (PreH1 : (i < 10)) (PreH2 : (0 <= i)) (PreH3 : (i <= 10)) (PreH4 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH5 : (vertex_valid g_low_level_spec source_pre )) (PreH6 : (nonnegative_edges g_low_level_spec )) (PreH7 : (0 < heap_capacity)) (PreH8 : (100000 <= heap_capacity)) (PreH9 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH10 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH11 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH12 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) i 10 )
|--
  “ (i < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 10) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((( &( "queue_pos" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "queue_pos" ) ) (i + 1 ) 10 )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000 )
  **  (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z ((-1)) (i)) )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure := 
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ (partial_map_absent queue_map_empty source_pre ) ” 
  &&  “ (source_pre < 10) ” 
  &&  “ (0 <= source_pre) ”
) \/
(
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (queue_size = 0)) (PreH10 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH11 : (vertex_valid g_low_level_spec source_pre )) (PreH12 : (nonnegative_edges g_low_level_spec )) (PreH13 : (0 < heap_capacity)) (PreH14 : (100000 <= heap_capacity)) (PreH15 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH16 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH17 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH18 : (visited_set_empty visited_init )) (PreH19 : (queue_map_empty = partial_map_empty)) (PreH20 : (partial_map_absent queue_map_empty source_pre )) (PreH21 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH22 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= source_pre) ” 
  &&  “ (source_pre < 10) ”
).

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure_split_goal_1 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (queue_size = 0)) (PreH10 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH11 : (vertex_valid g_low_level_spec source_pre )) (PreH12 : (nonnegative_edges g_low_level_spec )) (PreH13 : (0 < heap_capacity)) (PreH14 : (100000 <= heap_capacity)) (PreH15 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH16 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH17 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH18 : (visited_set_empty visited_init )) (PreH19 : (queue_map_empty = partial_map_empty)) (PreH20 : (partial_map_absent queue_map_empty source_pre )) (PreH21 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH22 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= source_pre) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure_split_goal_2 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size <= INT_MAX)) (PreH2 : (edge_count_pre <= INT_MAX)) (PreH3 : (source_pre <= INT_MAX)) (PreH4 : (vertex_count_pre <= INT_MAX)) (PreH5 : (queue_size >= INT_MIN)) (PreH6 : (edge_count_pre >= INT_MIN)) (PreH7 : (source_pre >= INT_MIN)) (PreH8 : (vertex_count_pre >= INT_MIN)) (PreH9 : (queue_size = 0)) (PreH10 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH11 : (vertex_valid g_low_level_spec source_pre )) (PreH12 : (nonnegative_edges g_low_level_spec )) (PreH13 : (0 < heap_capacity)) (PreH14 : (100000 <= heap_capacity)) (PreH15 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH16 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH17 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH18 : (visited_set_empty visited_init )) (PreH19 : (queue_map_empty = partial_map_empty)) (PreH20 : (partial_map_absent queue_map_empty source_pre )) (PreH21 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH22 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (source_pre < 10) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_init: (Z -> Prop)) (dist_init: (@list Z)) (queue_map_initial_after: partial_map) (queue_size: Z) (queue_map_empty: partial_map) (PreH1 : (queue_size = 0)) (PreH2 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH3 : (vertex_valid g_low_level_spec source_pre )) (PreH4 : (nonnegative_edges g_low_level_spec )) (PreH5 : (0 < heap_capacity)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (dijkstra_init_dist vertex_count_pre source_pre dist_init )) (PreH9 : (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec )) (PreH10 : (visited_set_empty visited_init )) (PreH11 : (queue_map_empty = partial_map_empty)) (PreH12 : (partial_map_absent queue_map_empty source_pre )) (PreH13 : (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 )) (PreH14 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty 0 )
|--
  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ (partial_map_absent queue_map_empty source_pre ) ” 
  &&  “ (source_pre < 10) ” 
  &&  “ (0 <= source_pre) ” 
  &&  “ (queue_size = 0) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (dijkstra_init_dist vertex_count_pre source_pre dist_init ) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (visited_set_empty visited_init ) ” 
  &&  “ (queue_map_empty = partial_map_empty) ” 
  &&  “ (partial_map_absent queue_map_empty source_pre ) ” 
  &&  “ (dk_map_queue_push_result queue_map_empty queue_map_initial_after source_pre 0 ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_empty queue_size )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_init )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3 := dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure -> dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_aux.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4_pure := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_size: Z) (queue_map: partial_map) (PreH1 : (0 < queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH9 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH10 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
  **  ((( &( "cur_vertex" ) )) # Int  |->_)
  **  ((( &( "cur_distance" ) )) # Int  |->_)
|--
  “ (1 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_size: Z) (queue_map: partial_map) (PreH1 : (0 < queue_size)) (PreH2 : (queue_size <= 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map )) (PreH9 : (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec )) (PreH10 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (1 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ (0 < queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map ) ” 
  &&  “ (dijkstra_dk_map_loop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4 := dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4_pure -> dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4_aux.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_5 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (dist_cur: (@list Z)) (queue_map_before: partial_map) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (100000 <= heap_capacity)) (PreH4 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH5 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH6 : (vertex_valid g_low_level_spec source_pre )) (PreH7 : (nonnegative_edges g_low_level_spec )) (PreH8 : (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map_before )) (PreH9 : (storage_index cur_vertex )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (cur_vertex < 10)) (PreH13 : (0 <= cur_distance)) (PreH14 : (cur_distance <= 1000000000)) (PreH15 : (dk_map_queue_pop_result queue_map_before queue_map cur_vertex cur_distance )) (PreH16 : (dijkstra_dk_map_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map cur_vertex cur_distance X_low_level_spec )) (PreH17 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (dijkstra_dk_map_loop_state g_low_level_spec source_pre visited_cur dist_cur queue_map_before ) ” 
  &&  “ (storage_index cur_vertex ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (cur_vertex < 10) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (dk_map_queue_pop_result queue_map_before queue_map cur_vertex cur_distance ) ” 
  &&  “ (dijkstra_dk_map_after_pop_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_cur dist_cur queue_map cur_vertex cur_distance X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((head_pre + (cur_vertex * sizeof(INT)))) # Int  |-> (Znth cur_vertex head_values_low_level_spec 0))
  **  (IntArray.missing_i head_pre cur_vertex 0 vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_cur )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_6 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge <> (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH18 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (edge <> (-1)) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map ) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((to_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge to_values_low_level_spec 0))
  **  (IntArray.missing_i to_pre edge 0 edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_7 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (edge: Z) (dist_edge: (@list Z)) (queue_map: partial_map) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (cur_distance: Z) (cur_vertex: Z) (queue_size: Z) (PreH1 : (edge <> (-1))) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size <= 100000)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH14 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH18 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (edge <> (-1)) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 <= cur_vertex) ” 
  &&  “ (cur_vertex < vertex_count_pre) ” 
  &&  “ (0 <= cur_distance) ” 
  &&  “ (cur_distance <= 1000000000) ” 
  &&  “ (visited_set_add visited_cur cur_vertex visited_edge ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map ) ” 
  &&  “ (0 <= edge) ” 
  &&  “ (edge < edge_count_pre) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((weight_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge weight_values_low_level_spec 0))
  **  (IntArray.missing_i weight_pre edge 0 edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_8 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance <= (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (0 <= queue_size)) (PreH4 : (queue_size <= 100000)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (0 <= cur_distance)) (PreH13 : (cur_distance <= 1000000000)) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH17 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH18 : (0 <= neighbor)) (PreH19 : (neighbor < vertex_count_pre)) (PreH20 : (neighbor < 10)) (PreH21 : (0 <= edge_weight)) (PreH22 : (edge_weight <= 1000000000)) (PreH23 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH24 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH25 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH26 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (cur_distance <= (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((dist_pre + (neighbor * sizeof(INT)))) # Int  |-> (Znth neighbor dist_edge 0))
  **  (IntArray.missing_i dist_pre neighbor 0 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_9 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (0 <= queue_size)) (PreH5 : (queue_size <= 100000)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH9 : (vertex_valid g_low_level_spec source_pre )) (PreH10 : (nonnegative_edges g_low_level_spec )) (PreH11 : (0 <= cur_vertex)) (PreH12 : (cur_vertex < vertex_count_pre)) (PreH13 : (0 <= cur_distance)) (PreH14 : (cur_distance <= 1000000000)) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH18 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH19 : (0 <= neighbor)) (PreH20 : (neighbor < vertex_count_pre)) (PreH21 : (neighbor < 10)) (PreH22 : (0 <= edge_weight)) (PreH23 : (edge_weight <= 1000000000)) (PreH24 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH25 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH26 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH27 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ ((cur_distance + edge_weight ) < (Znth neighbor dist_edge 0)) ” 
  &&  “ (cur_distance <= (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((dist_pre + (neighbor * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre neighbor 0 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10_pure := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (queue_size < heap_capacity)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (candidate = (cur_distance + edge_weight ))) (PreH23 : (0 <= candidate)) (PreH24 : (candidate <= 1000000000)) (PreH25 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH26 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before )) (PreH27 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec )) (PreH28 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH29 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH30 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  ((( &( "vertex_count" ) )) # Int  |-> vertex_count_pre)
  **  ((( &( "source" ) )) # Int  |-> source_pre)
  **  ((( &( "edge_count" ) )) # Int  |-> edge_count_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "weight" ) )) # Ptr  |-> weight_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "queue_size" ) )) # Int  |-> queue_size)
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
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
|--
  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (partial_map_update_or_add_pre queue_map_before neighbor candidate ) ”
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10_aux := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (PreH1 : (0 <= queue_size)) (PreH2 : (queue_size < 100000)) (PreH3 : (queue_size < heap_capacity)) (PreH4 : (100000 <= heap_capacity)) (PreH5 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH6 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH7 : (vertex_valid g_low_level_spec source_pre )) (PreH8 : (nonnegative_edges g_low_level_spec )) (PreH9 : (0 <= cur_vertex)) (PreH10 : (cur_vertex < vertex_count_pre)) (PreH11 : (0 <= cur_distance)) (PreH12 : (cur_distance <= 1000000000)) (PreH13 : (0 <= edge)) (PreH14 : (edge < edge_count_pre)) (PreH15 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH16 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH17 : (0 <= neighbor)) (PreH18 : (neighbor < vertex_count_pre)) (PreH19 : (neighbor < 10)) (PreH20 : (0 <= edge_weight)) (PreH21 : (edge_weight <= 1000000000)) (PreH22 : (candidate = (cur_distance + edge_weight ))) (PreH23 : (0 <= candidate)) (PreH24 : (candidate <= 1000000000)) (PreH25 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH26 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before )) (PreH27 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec )) (PreH28 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH29 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH30 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
|--
  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ (0 <= neighbor) ” 
  &&  “ (neighbor < 10) ” 
  &&  “ (partial_map_update_or_add_pre queue_map_before neighbor candidate ) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (queue_size < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before ) ” 
  &&  “ (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec ) ” 
  &&  “ (partial_map_update_or_add_pre queue_map_before neighbor candidate ) ” 
  &&  “ (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map_before queue_size )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10 := dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10_pure -> dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10_aux.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_11 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_after: (@list Z)) (queue_map_after: partial_map) (queue_size_after: Z) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (candidate: Z) (queue_map_before: partial_map) (n_after: Z) (PreH1 : (partial_map_update_or_add_size queue_map_before queue_size n_after neighbor candidate )) (PreH2 : (0 <= queue_size)) (PreH3 : (queue_size < 100000)) (PreH4 : (queue_size < heap_capacity)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (0 <= cur_distance)) (PreH13 : (cur_distance <= 1000000000)) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH17 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH18 : (0 <= neighbor)) (PreH19 : (neighbor < vertex_count_pre)) (PreH20 : (neighbor < 10)) (PreH21 : (0 <= edge_weight)) (PreH22 : (edge_weight <= 1000000000)) (PreH23 : (candidate = (cur_distance + edge_weight ))) (PreH24 : (0 <= candidate)) (PreH25 : (candidate <= 1000000000)) (PreH26 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH27 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before )) (PreH28 : (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec )) (PreH29 : (partial_map_update_or_add_pre queue_map_before neighbor candidate )) (PreH30 : (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate )) (PreH31 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 (partial_map_update_or_add (queue_map_before) (neighbor) (candidate)) n_after )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
|--
  “ (partial_map_update_or_add_size queue_map_before queue_size n_after neighbor candidate ) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size < 100000) ” 
  &&  “ (queue_size < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_after queue_map_before ) ” 
  &&  “ (dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre cur_vertex cur_distance edge neighbor candidate head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_after queue_map_before X_low_level_spec ) ” 
  &&  “ (partial_map_update_or_add_pre queue_map_before neighbor candidate ) ” 
  &&  “ (dk_map_queue_update_or_push_result queue_map_before queue_map_after queue_size queue_size_after neighbor candidate ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((next_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge next_values_low_level_spec 0))
  **  (IntArray.missing_i next_pre edge 0 edge_count_pre next_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 (partial_map_update_or_add (queue_map_before) (neighbor) (candidate)) n_after )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_after )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_12 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : ((cur_distance + edge_weight ) >= (Znth neighbor dist_edge 0))) (PreH2 : (cur_distance <= (1000000000 - edge_weight ))) (PreH3 : (edge_weight >= 0)) (PreH4 : (0 <= queue_size)) (PreH5 : (queue_size <= 100000)) (PreH6 : (100000 <= heap_capacity)) (PreH7 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH8 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH9 : (vertex_valid g_low_level_spec source_pre )) (PreH10 : (nonnegative_edges g_low_level_spec )) (PreH11 : (0 <= cur_vertex)) (PreH12 : (cur_vertex < vertex_count_pre)) (PreH13 : (0 <= cur_distance)) (PreH14 : (cur_distance <= 1000000000)) (PreH15 : (0 <= edge)) (PreH16 : (edge < edge_count_pre)) (PreH17 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH18 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH19 : (0 <= neighbor)) (PreH20 : (neighbor < vertex_count_pre)) (PreH21 : (neighbor < 10)) (PreH22 : (0 <= edge_weight)) (PreH23 : (edge_weight <= 1000000000)) (PreH24 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH25 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH26 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH27 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ ((cur_distance + edge_weight ) >= (Znth neighbor dist_edge 0)) ” 
  &&  “ (cur_distance <= (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((next_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge next_values_low_level_spec 0))
  **  (IntArray.missing_i next_pre edge 0 edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
.

Definition dijkstra_linked_forward_star_decrease_key_partial_solve_wit_13 := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (next_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (head_values_low_level_spec: (@list Z)) (g_low_level_spec: G) (visited_cur: (Z -> Prop)) (visited_edge: (Z -> Prop)) (dist_edge: (@list Z)) (queue_map: partial_map) (queue_size: Z) (cur_vertex: Z) (cur_distance: Z) (edge: Z) (neighbor: Z) (edge_weight: Z) (PreH1 : (cur_distance > (1000000000 - edge_weight ))) (PreH2 : (edge_weight >= 0)) (PreH3 : (0 <= queue_size)) (PreH4 : (queue_size <= 100000)) (PreH5 : (100000 <= heap_capacity)) (PreH6 : ((edge_count_pre + 1 ) <= heap_capacity)) (PreH7 : (graph_has_size g_low_level_spec vertex_count_pre )) (PreH8 : (vertex_valid g_low_level_spec source_pre )) (PreH9 : (nonnegative_edges g_low_level_spec )) (PreH10 : (0 <= cur_vertex)) (PreH11 : (cur_vertex < vertex_count_pre)) (PreH12 : (0 <= cur_distance)) (PreH13 : (cur_distance <= 1000000000)) (PreH14 : (0 <= edge)) (PreH15 : (edge < edge_count_pre)) (PreH16 : (neighbor = (Znth (edge) (to_values_low_level_spec) (0)))) (PreH17 : (edge_weight = (Znth (edge) (weight_values_low_level_spec) (0)))) (PreH18 : (0 <= neighbor)) (PreH19 : (neighbor < vertex_count_pre)) (PreH20 : (neighbor < 10)) (PreH21 : (0 <= edge_weight)) (PreH22 : (edge_weight <= 1000000000)) (PreH23 : (visited_set_add visited_cur cur_vertex visited_edge )) (PreH24 : (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map )) (PreH25 : (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec )) (PreH26 : (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec )) ,
  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
|--
  “ (cur_distance > (1000000000 - edge_weight )) ” 
  &&  “ (edge_weight >= 0) ” 
  &&  “ (0 <= queue_size) ” 
  &&  “ (queue_size <= 100000) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
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
  &&  “ (dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge dist_edge queue_map ) ” 
  &&  “ (dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex cur_distance edge head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec visited_edge dist_edge queue_map X_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (((next_pre + (edge * sizeof(INT)))) # Int  |-> (Znth edge next_values_low_level_spec 0))
  **  (IntArray.missing_i next_pre edge 0 edge_count_pre next_values_low_level_spec )
  **  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_edge )
  **  (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT))) 10 100000 queue_map queue_size )
.

Definition dijkstra_linked_forward_star_decrease_key_derive_high_level_spec_by_low_level_spec := 
forall (dist_pre: Z) (next_pre: Z) (weight_pre: Z) (to_pre: Z) (head_pre: Z) (edge_count_pre: Z) (source_pre: Z) (vertex_count_pre: Z) (dist0_high_level_spec: (@list Z)) (g_high_level_spec: G) ,
  “ (graph_has_size g_high_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_high_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_high_level_spec ) ” 
  &&  “ (shortest_path_relaxation_bounded g_high_level_spec source_pre 1000000000 ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (0 <= edge_count_pre) ” 
  &&  “ (edge_count_pre <= 100000) ” 
  &&  “ (vector_shape dist0_high_level_spec ) ”
  &&  (GraphForwardStar.store_graph g_high_level_spec edge_count_pre head_pre to_pre weight_pre next_pre )
  **  (IntArray.full dist_pre 10 dist0_high_level_spec )
|--
EX (g_low_level_spec: G) (head_values_low_level_spec: (@list Z)) (to_values_low_level_spec: (@list Z)) (weight_values_low_level_spec: (@list Z)) (next_values_low_level_spec: (@list Z)) (dist0_low_level_spec: (@list Z)) (X_low_level_spec: (unit -> (state -> Prop))) ,
  (“ (graph_has_size g_low_level_spec vertex_count_pre ) ” 
  &&  “ (vertex_valid g_low_level_spec source_pre ) ” 
  &&  “ (nonnegative_edges g_low_level_spec ) ” 
  &&  “ (0 < heap_capacity) ” 
  &&  “ (100000 <= heap_capacity) ” 
  &&  “ ((edge_count_pre + 1 ) <= heap_capacity) ” 
  &&  “ (0 <= edge_count_pre) ” 
  &&  “ (edge_count_pre <= 100000) ” 
  &&  “ (dijkstra_dk_lfs_initial_refines g_low_level_spec source_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec X_low_level_spec ) ” 
  &&  “ (vector_shape dist0_low_level_spec ) ” 
  &&  “ (forward_star_model g_low_level_spec edge_count_pre head_values_low_level_spec to_values_low_level_spec weight_values_low_level_spec next_values_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist0_low_level_spec ))
  **
  ((EX visited_out dist_out_2,
  “ (safeExec (graph_state_model (g_low_level_spec) (visited_out) (dist_out_2)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full head_pre vertex_count_pre head_values_low_level_spec )
  **  (IntArray.full to_pre edge_count_pre to_values_low_level_spec )
  **  (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec )
  **  (IntArray.full next_pre edge_count_pre next_values_low_level_spec )
  **  (IntArray.full dist_pre 10 dist_out_2 ))
  -*
  (EX dist_out,
  “ (dijkstra_shortest_dist g_high_level_spec source_pre dist_out ) ”
  &&  (GraphForwardStar.store_graph g_high_level_spec edge_count_pre head_pre to_pre weight_pre next_pre )
  **  (IntArray.full dist_pre 10 dist_out )))
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
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_1 : dijkstra_linked_forward_star_decrease_key_safety_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_2 : dijkstra_linked_forward_star_decrease_key_safety_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_3 : dijkstra_linked_forward_star_decrease_key_safety_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_4 : dijkstra_linked_forward_star_decrease_key_safety_wit_4.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_5 : dijkstra_linked_forward_star_decrease_key_safety_wit_5.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_6 : dijkstra_linked_forward_star_decrease_key_safety_wit_6.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_7 : dijkstra_linked_forward_star_decrease_key_safety_wit_7.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_8 : dijkstra_linked_forward_star_decrease_key_safety_wit_8.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_9 : dijkstra_linked_forward_star_decrease_key_safety_wit_9.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_10 : dijkstra_linked_forward_star_decrease_key_safety_wit_10.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_11 : dijkstra_linked_forward_star_decrease_key_safety_wit_11.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_12 : dijkstra_linked_forward_star_decrease_key_safety_wit_12.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_13 : dijkstra_linked_forward_star_decrease_key_safety_wit_13.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_14 : dijkstra_linked_forward_star_decrease_key_safety_wit_14.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_15 : dijkstra_linked_forward_star_decrease_key_safety_wit_15.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_16 : dijkstra_linked_forward_star_decrease_key_safety_wit_16.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_17 : dijkstra_linked_forward_star_decrease_key_safety_wit_17.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_18 : dijkstra_linked_forward_star_decrease_key_safety_wit_18.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_19 : dijkstra_linked_forward_star_decrease_key_safety_wit_19.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_20 : dijkstra_linked_forward_star_decrease_key_safety_wit_20.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_21 : dijkstra_linked_forward_star_decrease_key_safety_wit_21.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_22 : dijkstra_linked_forward_star_decrease_key_safety_wit_22.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_23 : dijkstra_linked_forward_star_decrease_key_safety_wit_23.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_24 : dijkstra_linked_forward_star_decrease_key_safety_wit_24.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_25 : dijkstra_linked_forward_star_decrease_key_safety_wit_25.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_26 : dijkstra_linked_forward_star_decrease_key_safety_wit_26.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_27 : dijkstra_linked_forward_star_decrease_key_safety_wit_27.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_28 : dijkstra_linked_forward_star_decrease_key_safety_wit_28.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_29 : dijkstra_linked_forward_star_decrease_key_safety_wit_29.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_30 : dijkstra_linked_forward_star_decrease_key_safety_wit_30.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_safety_wit_31 : dijkstra_linked_forward_star_decrease_key_safety_wit_31.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_1 : dijkstra_linked_forward_star_decrease_key_entail_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_2 : dijkstra_linked_forward_star_decrease_key_entail_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_3 : dijkstra_linked_forward_star_decrease_key_entail_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_4 : dijkstra_linked_forward_star_decrease_key_entail_wit_4.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_5 : dijkstra_linked_forward_star_decrease_key_entail_wit_5.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_6 : dijkstra_linked_forward_star_decrease_key_entail_wit_6.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_7 : dijkstra_linked_forward_star_decrease_key_entail_wit_7.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_8 : dijkstra_linked_forward_star_decrease_key_entail_wit_8.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_9 : dijkstra_linked_forward_star_decrease_key_entail_wit_9.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_10 : dijkstra_linked_forward_star_decrease_key_entail_wit_10.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_11_1 : dijkstra_linked_forward_star_decrease_key_entail_wit_11_1.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_11_2 : dijkstra_linked_forward_star_decrease_key_entail_wit_11_2.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_11_3 : dijkstra_linked_forward_star_decrease_key_entail_wit_11_3.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_12 : dijkstra_linked_forward_star_decrease_key_entail_wit_12.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_13 : dijkstra_linked_forward_star_decrease_key_entail_wit_13.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_return_wit_1 : dijkstra_linked_forward_star_decrease_key_return_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_2 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_2.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4_pure : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4_pure.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_4.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_5 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_5.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_6 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_6.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_7 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_7.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_8 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_8.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_9 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_9.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10_pure : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10_pure.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_10.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_11 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_11.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_12 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_12.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_13 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_13.
Axiom proof_of_dijkstra_linked_forward_star_decrease_key_derive_high_level_spec_by_low_level_spec : dijkstra_linked_forward_star_decrease_key_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
