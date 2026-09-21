#include "safeexec_def.h"
#include "Data_structures/priority_queue_decrease_key/priority_queue_decrease_key_def.h"

#define MAX_VERTEX_COUNT 10
#define INF 1000000000
#define MAX_PRIORITY_QUEUE_SIZE 100000

/*@ Import Coq Require Import Algorithms.Dijkstra.Dijkstra */
/*@ Import Coq From GraphLib Require Import Zweight */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_decrease_key_lib */
/*@ Import Coq Import DijkstraGraph */
/*@ Import Coq Import DijkstraLinkedForwardStar */
/*@ Import Coq Import DijkstraDecreaseKey */

/*@ Extern Coq (G :: *) */
/*@ Extern Coq (state :: *) */
/*@ Extern Coq
      (dijkstra_init_dist : Z -> Z -> list Z -> Prop)
      (dijkstra_shortest_dist : G -> Z -> list Z -> Prop)
      (nonnegative_edges : G -> Prop)
      (shortest_path_relaxation_bounded : G -> Z -> Z -> Prop)
      (dist_init_loop : Z -> list Z -> Prop)
	      (graph_state_model : G -> (Z -> Prop) -> list Z -> state -> Prop)
	      (visited_set_empty : (Z -> Prop) -> Prop)
	      (visited_set_add : (Z -> Prop) -> Z -> (Z -> Prop) -> Prop)
	      (dijkstra_dk_lfs_initial_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (unit -> state -> Prop) -> Prop)
      (vector_shape : list Z -> Prop)
      (graph_has_size : G -> Z -> Prop)
      (vertex_valid : G -> Z -> Prop)
      (forward_star_model :
        G -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (storage_index : Z -> Prop)
      (partial_map_empty : partial_map)
      (GraphForwardStar::store_graph :
        G -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (partial_map_absent :
        partial_map -> Z -> Prop)
      (partial_map_update_or_add_pre :
        partial_map -> Z -> Z -> Prop)
	      (dk_map_queue_push_result :
	        partial_map -> partial_map -> Z -> Z -> Prop)
	      (dk_map_queue_pop_result :
	        partial_map -> partial_map -> Z -> Z -> Prop)
	      (dk_map_queue_update_or_push_result :
	        partial_map -> partial_map ->
	        Z -> Z -> Z -> Z -> Prop)
	      (dijkstra_dk_map_loop_state :
	        G -> Z -> (Z -> Prop) -> list Z -> partial_map -> Prop)
	      (dijkstra_dk_map_edge_loop_state :
	        G -> Z -> (Z -> Prop) -> Z -> Z -> Z ->
	        list Z -> partial_map -> Prop)
	      (dijkstra_dk_map_loop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> partial_map ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_dk_map_after_pop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> partial_map -> Z -> Z ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_dk_map_edge_loop_refines :
	        G -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> partial_map ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_dk_map_after_relax_refines :
	        G -> Z -> Z -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> partial_map ->
	        (unit -> state -> Prop) -> Prop)
 */

void dijkstra_linked_forward_star_init(int vertex_count, int source, int *dist)
/*@ With (dist0 : list Z)
    Require
	      0 < vertex_count && vertex_count <= MAX_VERTEX_COUNT &&
	      0 <= source && source < vertex_count &&
	      vector_shape(dist0) &&
	      IntArray::full(dist, MAX_VERTEX_COUNT, dist0)
    Ensure
      exists dist1,
        dijkstra_init_dist(vertex_count, source, dist1) &&
        IntArray::full(dist, MAX_VERTEX_COUNT, dist1)
 */
{
  /*@ Inv Assert
      exists dist_cur,
        vertex_count == vertex_count@pre && source == source@pre &&
        dist == dist@pre &&
        0 < vertex_count@pre && vertex_count@pre <= MAX_VERTEX_COUNT &&
        0 <= source@pre && source@pre < vertex_count@pre &&
	        0 <= i && i <= MAX_VERTEX_COUNT &&
	        dist_init_loop(i, dist_cur) &&
        IntArray::full(dist@pre, MAX_VERTEX_COUNT, dist_cur)
   */
	  for (int i = 0; i < MAX_VERTEX_COUNT; ++i) {
    dist[i] = INF;
  }



  dist[source] = 0;
}

void dijkstra_linked_forward_star_decrease_key(int vertex_count, int source, int edge_count,
                                  int *head, int *to, int *weight, int *next,
                                  int *dist)
/*@ high_level_spec <= low_level_spec
    With (g : G) (dist0 : list Z)
    Require
      graph_has_size(g, vertex_count) &&
      vertex_valid(g, source) &&
      nonnegative_edges(g) &&
      shortest_path_relaxation_bounded(g, source, INF) &&
      0 < heap_capacity &&
      MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
      edge_count + 1 <= heap_capacity &&
      0 <= edge_count && edge_count <= MAX_PRIORITY_QUEUE_SIZE &&
      vector_shape(dist0) &&
      GraphForwardStar::store_graph(g, edge_count, head, to, weight, next) *
      IntArray::full(dist, MAX_VERTEX_COUNT, dist0)
    Ensure
      exists dist_out,
        dijkstra_shortest_dist(g, source, dist_out) &&
        GraphForwardStar::store_graph(g, edge_count, head, to, weight, next) *
        IntArray::full(dist, MAX_VERTEX_COUNT, dist_out)
 */
;

void dijkstra_linked_forward_star_decrease_key(int vertex_count, int source, int edge_count,
                                  int *head, int *to, int *weight, int *next,
                                  int *dist)
/*@ low_level_spec
    With (g : G) (head_values to_values weight_values next_values : list Z)
         (dist0 : list Z) X
    Require
      graph_has_size(g, vertex_count) &&
	      vertex_valid(g, source) &&
      nonnegative_edges(g) &&
      0 < heap_capacity &&
      MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
      edge_count + 1 <= heap_capacity &&
      0 <= edge_count && edge_count <= MAX_PRIORITY_QUEUE_SIZE &&
		      dijkstra_dk_lfs_initial_refines(g, source,
		        head_values, to_values, weight_values, next_values, X) &&
		      vector_shape(dist0) &&
	      forward_star_model(g, edge_count,
	        head_values, to_values, weight_values, next_values) &&
	      IntArray::full(head, vertex_count, head_values) *
	      IntArray::full(to, edge_count, to_values) *
	      IntArray::full(weight, edge_count, weight_values) *
	      IntArray::full(next, edge_count, next_values) *
	      IntArray::full(dist, MAX_VERTEX_COUNT, dist0)
	    Ensure
		      exists visited_out dist_out,
		        safeExec(graph_state_model(g, visited_out, dist_out), return(tt), X) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_out)
 */
{
  dijkstra_linked_forward_star_init(vertex_count, source, dist);
  int queue_key[MAX_PRIORITY_QUEUE_SIZE];
  int queue_data[MAX_PRIORITY_QUEUE_SIZE];
  int queue_pos[MAX_VERTEX_COUNT];

  /*@ Inv Assert
      exists dist_init,
      vertex_count == vertex_count@pre && source == source@pre &&
      edge_count == edge_count@pre &&
      head == head@pre && to == to@pre &&
      weight == weight@pre && next == next@pre && dist == dist@pre &&
      0 <= i && i <= MAX_VERTEX_COUNT &&
      graph_has_size(g, vertex_count) &&
      vertex_valid(g, source) &&
      nonnegative_edges(g) &&
      0 < heap_capacity &&
      MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
      edge_count + 1 <= heap_capacity &&
      dijkstra_init_dist(vertex_count, source, dist_init) &&
      dijkstra_dk_lfs_initial_refines(g, source,
        head_values, to_values, weight_values, next_values, X) &&
      forward_star_model(g, edge_count,
        head_values, to_values, weight_values, next_values) &&
      IntArray::full(head, vertex_count, head_values) *
      IntArray::full(to, edge_count, to_values) *
      IntArray::full(weight, edge_count, weight_values) *
      IntArray::full(next, edge_count, next_values) *
      IntArray::full(dist, MAX_VERTEX_COUNT, dist_init) *
      IntArray::undef_seg(pointer_offset(queue_key, 0, sizeof(int), int), 0, MAX_PRIORITY_QUEUE_SIZE) *
      IntArray::undef_seg(pointer_offset(queue_data, 0, sizeof(int), int), 0, MAX_PRIORITY_QUEUE_SIZE) *
      IntArray::full(queue_pos, i, repeat_Z(-1, i)) *
      IntArray::undef_seg(queue_pos, i, MAX_VERTEX_COUNT)
   */
  for (int i = 0; i < MAX_VERTEX_COUNT; ++i) {
    queue_pos[i] = -1;
  }


  int queue_size = 0;

	  /*@ Assert
	      exists visited_init dist_init queue_map_empty queue_map_initial_after,
	        vertex_count == vertex_count@pre && source == source@pre &&
        edge_count == edge_count@pre &&
        head == head@pre && to == to@pre &&
        weight == weight@pre && next == next@pre && dist == dist@pre &&
        queue_size == 0 &&
	        graph_has_size(g, vertex_count) &&
	        vertex_valid(g, source) &&
	        nonnegative_edges(g) &&
	        0 < heap_capacity &&
	        MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
	        edge_count + 1 <= heap_capacity &&
	        dijkstra_init_dist(vertex_count, source, dist_init) &&
	        dijkstra_dk_lfs_initial_refines(g, source,
	          head_values, to_values, weight_values, next_values, X) &&
		        visited_set_empty(visited_init) &&
		        queue_map_empty == partial_map_empty &&
		        partial_map_absent(
		          queue_map_empty, source) &&
		        dk_map_queue_push_result(
		          queue_map_empty, queue_map_initial_after, source, 0) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_init) *
	        store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), pointer_offset(queue_pos, 0, sizeof(int), int), MAX_VERTEX_COUNT, MAX_PRIORITY_QUEUE_SIZE, queue_map_empty, 0)
   */
  /*@ Given queue_map_empty */
  pqdk_push(queue_key, queue_data, queue_pos, &queue_size, MAX_VERTEX_COUNT, source, 0)
    /*@ where M_before = queue_map_empty, n = queue_size, capacity = MAX_PRIORITY_QUEUE_SIZE */;
  
	  /*@ Inv Assert
	      exists visited_cur dist_cur queue_map,
	        vertex_count == vertex_count@pre && source == source@pre &&
        edge_count == edge_count@pre &&
        head == head@pre && to == to@pre &&
        weight == weight@pre && next == next@pre && dist == dist@pre &&
        0 <= queue_size && queue_size <= MAX_PRIORITY_QUEUE_SIZE &&
        MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
        edge_count + 1 <= heap_capacity &&
	        graph_has_size(g, vertex_count) &&
	        vertex_valid(g, source) &&
	        nonnegative_edges(g) &&
		        dijkstra_dk_map_loop_state(g, source, visited_cur, dist_cur, queue_map) &&
		        dijkstra_dk_map_loop_refines(g, source,
		          head_values, to_values, weight_values, next_values,
		          visited_cur, dist_cur, queue_map, X) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
	        store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), pointer_offset(queue_pos, 0, sizeof(int), int), MAX_VERTEX_COUNT, MAX_PRIORITY_QUEUE_SIZE, queue_map, queue_size)
   */
  while (queue_size != 0) {
    int cur_vertex;
    int cur_distance;

    /*@ Given queue_map */
    pqdk_pop(queue_key, queue_data, queue_pos, &queue_size, MAX_VERTEX_COUNT, &cur_vertex, &cur_distance)
      /*@ where M_before = queue_map, n = queue_size, capacity = MAX_PRIORITY_QUEUE_SIZE */;
    
	    /*@ Assert
	        exists visited_cur dist_cur queue_map_before queue_map,
	          vertex_count == vertex_count@pre && source == source@pre &&
          edge_count == edge_count@pre &&
          head == head@pre && to == to@pre &&
          weight == weight@pre && next == next@pre && dist == dist@pre &&
          0 <= queue_size && queue_size < MAX_PRIORITY_QUEUE_SIZE &&
          MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
          edge_count + 1 <= heap_capacity &&
	          graph_has_size(g, vertex_count) &&
	          vertex_valid(g, source) &&
	          nonnegative_edges(g) &&
		          dijkstra_dk_map_loop_state(g, source, visited_cur, dist_cur,
		            queue_map_before) &&
		          storage_index(cur_vertex) &&
	          0 <= cur_vertex && cur_vertex < vertex_count &&
          cur_vertex < MAX_VERTEX_COUNT &&
          0 <= cur_distance && cur_distance <= INF &&
          dk_map_queue_pop_result(
            queue_map_before, queue_map, cur_vertex, cur_distance) &&
		          dijkstra_dk_map_after_pop_refines(g, source,
		            head_values, to_values, weight_values, next_values,
		            visited_cur, dist_cur, queue_map,
		            cur_vertex, cur_distance, X) &&
	          forward_star_model(g, edge_count,
	            head_values, to_values, weight_values, next_values) &&
	          IntArray::full(head, vertex_count, head_values) *
	          IntArray::full(to, edge_count, to_values) *
	          IntArray::full(weight, edge_count, weight_values) *
	          IntArray::full(next, edge_count, next_values) *
	          IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
	          store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), pointer_offset(queue_pos, 0, sizeof(int), int), MAX_VERTEX_COUNT, MAX_PRIORITY_QUEUE_SIZE, queue_map, queue_size)
     */

	  /*@ Inv Assert
	      exists visited_cur visited_edge dist_edge
	             queue_map,
	        vertex_count == vertex_count@pre && source == source@pre &&
        edge_count == edge_count@pre &&
        head == head@pre && to == to@pre &&
        weight == weight@pre && next == next@pre && dist == dist@pre &&
        0 <= queue_size && queue_size <= MAX_PRIORITY_QUEUE_SIZE &&
        MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
        edge_count + 1 <= heap_capacity &&
	        graph_has_size(g, vertex_count) &&
	        vertex_valid(g, source) &&
	        nonnegative_edges(g) &&
	        0 <= cur_vertex && cur_vertex < vertex_count &&
	        0 <= cur_distance && cur_distance <= INF &&
	        visited_set_add(visited_cur, cur_vertex, visited_edge) &&
	        dijkstra_dk_map_edge_loop_state(
	          g, source, visited_edge, cur_vertex, cur_distance, edge,
	          dist_edge, queue_map) &&
        (edge == -1 || (0 <= edge && edge < edge_count)) &&
	        dijkstra_dk_map_edge_loop_refines(g, source, cur_vertex,
	          cur_distance, edge, head_values, to_values, weight_values,
	          next_values, visited_edge, dist_edge, queue_map, X) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_edge) *
	        store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), pointer_offset(queue_pos, 0, sizeof(int), int), MAX_VERTEX_COUNT, MAX_PRIORITY_QUEUE_SIZE, queue_map, queue_size)
   */
  for (int edge = head[cur_vertex]; edge != -1; edge = next[edge]) {
    int neighbor = to[edge];
    int edge_weight = weight[edge];

	    /*@ Assert
	        exists visited_cur visited_edge dist_edge
	               queue_map,
	          vertex_count == vertex_count@pre && source == source@pre &&
          edge_count == edge_count@pre &&
          head == head@pre && to == to@pre &&
          weight == weight@pre && next == next@pre && dist == dist@pre &&
          0 <= queue_size && queue_size <= MAX_PRIORITY_QUEUE_SIZE &&
          MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
          edge_count + 1 <= heap_capacity &&
	          graph_has_size(g, vertex_count) &&
	          vertex_valid(g, source) &&
	          nonnegative_edges(g) &&
	          0 <= cur_vertex && cur_vertex < vertex_count &&
	          0 <= cur_distance && cur_distance <= INF &&
	          0 <= edge && edge < edge_count &&
          neighbor == Znth(edge, to_values, 0) &&
          edge_weight == Znth(edge, weight_values, 0) &&
	          0 <= neighbor && neighbor < vertex_count &&
	          neighbor < MAX_VERTEX_COUNT &&
	          0 <= edge_weight && edge_weight <= INF &&
	          visited_set_add(visited_cur, cur_vertex, visited_edge) &&
	          dijkstra_dk_map_edge_loop_state(
	            g, source, visited_edge, cur_vertex, cur_distance, edge,
	            dist_edge, queue_map) &&
	          dijkstra_dk_map_edge_loop_refines(g, source, cur_vertex,
	            cur_distance, edge, head_values, to_values, weight_values,
	            next_values, visited_edge, dist_edge, queue_map, X) &&
	          forward_star_model(g, edge_count,
	            head_values, to_values, weight_values, next_values) &&
	          IntArray::full(head, vertex_count, head_values) *
	          IntArray::full(to, edge_count, to_values) *
	          IntArray::full(weight, edge_count, weight_values) *
	          IntArray::full(next, edge_count, next_values) *
	          IntArray::full(dist, MAX_VERTEX_COUNT, dist_edge) *
	          store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), pointer_offset(queue_pos, 0, sizeof(int), int), MAX_VERTEX_COUNT, MAX_PRIORITY_QUEUE_SIZE, queue_map, queue_size)
     */

    if (edge_weight >= 0 && cur_distance <= INF - edge_weight) {
      int candidate = cur_distance + edge_weight;

      if (candidate < dist[neighbor]) {
        dist[neighbor] = candidate;
	        /*@ Assert
	            exists visited_cur visited_edge dist_after
	                   queue_map_before queue_map_after queue_size_after,
              vertex_count == vertex_count@pre &&
              source == source@pre &&
              edge_count == edge_count@pre &&
              head == head@pre && to == to@pre &&
              weight == weight@pre && next == next@pre &&
              dist == dist@pre &&
	            0 <= queue_size && queue_size < MAX_PRIORITY_QUEUE_SIZE &&
	            queue_size < heap_capacity &&
              MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
              edge_count + 1 <= heap_capacity &&
              graph_has_size(g, vertex_count) &&
              vertex_valid(g, source) &&
              nonnegative_edges(g) &&
	            0 <= cur_vertex && cur_vertex < vertex_count &&
	            0 <= cur_distance && cur_distance <= INF &&
	            0 <= edge && edge < edge_count &&
              neighbor == Znth(edge, to_values, 0) &&
              edge_weight == Znth(edge, weight_values, 0) &&
              0 <= neighbor && neighbor < vertex_count &&
              neighbor < MAX_VERTEX_COUNT &&
              0 <= edge_weight && edge_weight <= INF &&
	            candidate == cur_distance + edge_weight &&
	            0 <= candidate && candidate <= INF &&
	            visited_set_add(visited_cur, cur_vertex, visited_edge) &&
	            dijkstra_dk_map_edge_loop_state(
	              g, source, visited_edge, cur_vertex, cur_distance, edge,
	              dist_after, queue_map_before) &&
	            dijkstra_dk_map_after_relax_refines(g, source, cur_vertex,
	              cur_distance, edge, neighbor, candidate, head_values,
	              to_values, weight_values, next_values,
	              visited_edge, dist_after, queue_map_before, X) &&
	            partial_map_update_or_add_pre(
	              queue_map_before, neighbor, candidate) &&
              dk_map_queue_update_or_push_result(
                queue_map_before, queue_map_after,
                queue_size, queue_size_after, neighbor, candidate) &&
	            forward_star_model(g, edge_count,
	              head_values, to_values, weight_values, next_values) &&
	            IntArray::full(head, vertex_count, head_values) *
	            IntArray::full(to, edge_count, to_values) *
	            IntArray::full(weight, edge_count, weight_values) *
	            IntArray::full(next, edge_count, next_values) *
	            IntArray::full(dist, MAX_VERTEX_COUNT, dist_after) *
	            store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), pointer_offset(queue_pos, 0, sizeof(int), int), MAX_VERTEX_COUNT, MAX_PRIORITY_QUEUE_SIZE, queue_map_before, queue_size)
        */
        /*@ Given queue_map_before */
        pqdk_update_or_push(queue_key, queue_data, queue_pos, &queue_size, MAX_VERTEX_COUNT, neighbor, candidate)
          /*@ where M_before = queue_map_before, n = queue_size, capacity = MAX_PRIORITY_QUEUE_SIZE */;
      }
    }
  }
  }
  /*@ Assert
      exists visited_out dist_out queue_map_out,
        vertex_count == vertex_count@pre && source == source@pre &&
        edge_count == edge_count@pre &&
        head == head@pre && to == to@pre &&
        weight == weight@pre && next == next@pre && dist == dist@pre &&
        queue_size == 0 &&
        graph_has_size(g, vertex_count) &&
        vertex_valid(g, source) &&
        nonnegative_edges(g) &&
        MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
        edge_count + 1 <= heap_capacity &&
        dijkstra_dk_map_loop_state(g, source, visited_out, dist_out, queue_map_out) &&
        dijkstra_dk_map_loop_refines(g, source,
          head_values, to_values, weight_values, next_values,
          visited_out, dist_out, queue_map_out, X) &&
        forward_star_model(g, edge_count,
          head_values, to_values, weight_values, next_values) &&
        safeExec(graph_state_model(g, visited_out, dist_out), return(tt), X) &&
        IntArray::full(head, vertex_count, head_values) *
        IntArray::full(to, edge_count, to_values) *
        IntArray::full(weight, edge_count, weight_values) *
        IntArray::full(next, edge_count, next_values) *
        IntArray::full(dist, MAX_VERTEX_COUNT, dist_out) *
        IntArray::undef_full(queue_key, MAX_PRIORITY_QUEUE_SIZE) *
        IntArray::undef_full(queue_data, MAX_PRIORITY_QUEUE_SIZE) *
        IntArray::undef_full(queue_pos, MAX_VERTEX_COUNT)
   */
}
