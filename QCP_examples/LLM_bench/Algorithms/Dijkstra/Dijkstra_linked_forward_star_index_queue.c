#include "safeexec_def.h"
#include "Data_structures/priority_queue_index/priority_queue_index_def.h"

#define MAX_VERTEX_COUNT 10
#define INF 1000000000
#define MAX_PRIORITY_QUEUE_SIZE 100000

/*@ Import Coq Require Import Algorithms.Dijkstra.Dijkstra */
/*@ Import Coq From GraphLib Require Import Zweight */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_index_queue_lib */
/*@ Import Coq Import DijkstraGraph */
/*@ Import Coq Import DijkstraLinkedForwardStar */
/*@ Import Coq Import DijkstraIndexQueue */

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
	      (dijkstra_heap_lfs_initial_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (unit -> state -> Prop) -> Prop)
      (vector_shape : list Z -> Prop)
      (graph_has_size : G -> Z -> Prop)
      (vertex_valid : G -> Z -> Prop)
      (forward_star_model :
        G -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (storage_index : Z -> Prop)
      (GraphForwardStar::store_graph :
        G -> Z -> Z -> Z -> Z -> Z -> Assertion)
	      (index_queue_push_result :
	        multiset (Z * Z) -> multiset (Z * Z) -> Z -> Z -> Prop)
	      (index_queue_pop_result :
	        multiset (Z * Z) -> multiset (Z * Z) -> Z -> Z -> Prop)
	      (dijkstra_heap_loop_state :
	        G -> Z -> (Z -> Prop) -> list Z -> multiset (Z * Z) -> Prop)
	      (dijkstra_heap_edge_loop_state :
	        G -> Z -> (Z -> Prop) -> Z -> Z -> Z ->
	        list Z -> multiset (Z * Z) -> Prop)
	      (dijkstra_heap_loop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_heap_after_pop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) -> Z -> Z ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_heap_edge_loop_refines :
	        G -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_heap_after_relax_refines :
	        G -> Z -> Z -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) ->
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

  /*@ Assert
      exists dist_all_inf,
        vertex_count == vertex_count@pre && source == source@pre &&
        dist == dist@pre &&
        0 < vertex_count@pre && vertex_count@pre <= MAX_VERTEX_COUNT &&
        0 <= source@pre && source@pre < vertex_count@pre &&
	        dist_init_loop(MAX_VERTEX_COUNT, dist_all_inf) &&
        IntArray::full(dist@pre, MAX_VERTEX_COUNT, dist_all_inf)
   */

  dist[source] = 0;
}

void dijkstra_linked_forward_star_index_queue(int vertex_count, int source, int edge_count,
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

void dijkstra_linked_forward_star_index_queue(int vertex_count, int source, int edge_count,
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
		      dijkstra_heap_lfs_initial_refines(g, source,
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

	  /*@ Assert
	      exists dist_init,
	        vertex_count == vertex_count@pre && source == source@pre &&
	        edge_count == edge_count@pre &&
	        head == head@pre && to == to@pre &&
	        weight == weight@pre && next == next@pre && dist == dist@pre &&
	        graph_has_size(g, vertex_count) &&
	        vertex_valid(g, source) &&
	        nonnegative_edges(g) &&
	        0 < heap_capacity &&
	        MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
	        edge_count + 1 <= heap_capacity &&
	        dijkstra_init_dist(vertex_count, source, dist_init) &&
	        dijkstra_heap_lfs_initial_refines(g, source,
	          head_values, to_values, weight_values, next_values, X) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_init) *
	        IntArray::undef_seg(pointer_offset(queue_key, 0, sizeof(int), int), 0, MAX_PRIORITY_QUEUE_SIZE) *
        IntArray::undef_seg(pointer_offset(queue_data, 0, sizeof(int), int), 0, MAX_PRIORITY_QUEUE_SIZE)
   */
  int queue_size = 0;

	  /*@ Assert
	      exists visited_init dist_init queue_set_empty queue_set_initial_after,
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
	        dijkstra_heap_lfs_initial_refines(g, source,
	          head_values, to_values, weight_values, next_values, X) &&
		        visited_set_empty(visited_init) &&
		        queue_set_empty == list_to_multiset(nil) &&
		        index_queue_push_result(
		          queue_set_empty, queue_set_initial_after, source, 0) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_init) *
	        store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), queue_set_empty, 0)
   */
  /*@ Given queue_set_empty */
  push(queue_key, queue_data, queue_size, source, 0)
    /*@ where S_before = queue_set_empty */;
  queue_size = queue_size + 1;

	  /*@ Inv Assert
		      exists visited_cur dist_cur queue_set,
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
		        dijkstra_heap_loop_state(g, source, visited_cur, dist_cur, queue_set) &&
		        dijkstra_heap_loop_refines(g, source,
		          head_values, to_values, weight_values, next_values,
		          visited_cur, dist_cur, queue_set, X) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
	        store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), queue_set, queue_size)
   */
  while (queue_size != 0) {
    int cur_vertex;
    int cur_distance;
	    /*@ Assert
		        exists visited_cur dist_cur queue_set,
	          vertex_count == vertex_count@pre && source == source@pre &&
	          edge_count == edge_count@pre &&
	          head == head@pre && to == to@pre &&
	          weight == weight@pre && next == next@pre && dist == dist@pre &&
          0 < queue_size && queue_size <= MAX_PRIORITY_QUEUE_SIZE &&
          MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
          edge_count + 1 <= heap_capacity &&
	          graph_has_size(g, vertex_count) &&
	          vertex_valid(g, source) &&
	          nonnegative_edges(g) &&
		          dijkstra_heap_loop_state(g, source, visited_cur, dist_cur, queue_set) &&
		          dijkstra_heap_loop_refines(g, source,
		            head_values, to_values, weight_values, next_values,
	            visited_cur, dist_cur, queue_set, X) &&
	          forward_star_model(g, edge_count,
	            head_values, to_values, weight_values, next_values) &&
	          IntArray::full(head, vertex_count, head_values) *
	          IntArray::full(to, edge_count, to_values) *
	          IntArray::full(weight, edge_count, weight_values) *
	          IntArray::full(next, edge_count, next_values) *
	          IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
	          store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), queue_set, queue_size) *
          has_int_permission(&cur_vertex) *
          has_int_permission(&cur_distance)
     */
    /*@ Given queue_set */
    pop(queue_key, queue_data, queue_size, &cur_vertex, &cur_distance)
      /*@ where S_before = queue_set */;
    queue_size = queue_size - 1;

	    /*@ Assert
		        exists visited_cur dist_cur queue_set_before queue_set,
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
		          dijkstra_heap_loop_state(g, source, visited_cur, dist_cur,
		            queue_set_before) &&
		          storage_index(cur_vertex) &&
	          0 <= cur_vertex && cur_vertex < vertex_count &&
          cur_vertex < MAX_VERTEX_COUNT &&
          0 <= cur_distance && cur_distance <= INF &&
          index_queue_pop_result(
            queue_set_before, queue_set, cur_vertex, cur_distance) &&
		          dijkstra_heap_after_pop_refines(g, source,
		            head_values, to_values, weight_values, next_values,
		            visited_cur, dist_cur, queue_set,
		            cur_vertex, cur_distance, X) &&
	          forward_star_model(g, edge_count,
	            head_values, to_values, weight_values, next_values) &&
	          IntArray::full(head, vertex_count, head_values) *
	          IntArray::full(to, edge_count, to_values) *
	          IntArray::full(weight, edge_count, weight_values) *
	          IntArray::full(next, edge_count, next_values) *
	          IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
	          store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), queue_set, queue_size)
     */

    if (cur_distance == dist[cur_vertex]) {
	      /*@ Inv Assert
		          exists visited_cur visited_edge dist_edge
		                 queue_set,
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
	            dijkstra_heap_edge_loop_state(
	              g, source, visited_edge, cur_vertex, cur_distance, edge,
	              dist_edge, queue_set) &&
            (edge == -1 || (0 <= edge && edge < edge_count)) &&
		            dijkstra_heap_edge_loop_refines(g, source, cur_vertex,
		              cur_distance, edge, head_values, to_values, weight_values,
		              next_values, visited_edge, dist_edge, queue_set, X) &&
	            forward_star_model(g, edge_count,
	              head_values, to_values, weight_values, next_values) &&
	            IntArray::full(head, vertex_count, head_values) *
	            IntArray::full(to, edge_count, to_values) *
	            IntArray::full(weight, edge_count, weight_values) *
	            IntArray::full(next, edge_count, next_values) *
	            IntArray::full(dist, MAX_VERTEX_COUNT, dist_edge) *
	            store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), queue_set, queue_size)
       */
      for (int edge = head[cur_vertex]; edge != -1; edge = next[edge]) {
        int neighbor = to[edge];
        int edge_weight = weight[edge];

	        /*@ Assert
		            exists visited_cur visited_edge dist_edge
		                   queue_set,
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
	              dijkstra_heap_edge_loop_state(
	                g, source, visited_edge, cur_vertex, cur_distance, edge,
	                dist_edge, queue_set) &&
		              dijkstra_heap_edge_loop_refines(g, source, cur_vertex,
		                cur_distance, edge, head_values, to_values, weight_values,
		                next_values, visited_edge, dist_edge, queue_set, X) &&
	              forward_star_model(g, edge_count,
	                head_values, to_values, weight_values, next_values) &&
	              IntArray::full(head, vertex_count, head_values) *
	              IntArray::full(to, edge_count, to_values) *
	              IntArray::full(weight, edge_count, weight_values) *
	              IntArray::full(next, edge_count, next_values) *
	              IntArray::full(dist, MAX_VERTEX_COUNT, dist_edge) *
	              store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), queue_set, queue_size)
         */

        if (edge_weight >= 0 && cur_distance <= INF - edge_weight) {
          int candidate = cur_distance + edge_weight;

          if (candidate < dist[neighbor]) {
            dist[neighbor] = candidate;
	            /*@ Assert
	                exists visited_cur visited_edge dist_after
	                       queue_set_before queue_set_after,
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
		                  dijkstra_heap_edge_loop_state(
		                    g, source, visited_edge, cur_vertex, cur_distance, edge,
		                    dist_after, queue_set_before) &&
		                  dijkstra_heap_after_relax_refines(g, source, cur_vertex,
		                    cur_distance, edge, neighbor, candidate, head_values,
		                    to_values, weight_values, next_values,
		                    visited_edge, dist_after, queue_set_before, X) &&
                  index_queue_push_result(
                    queue_set_before, queue_set_after, neighbor, candidate) &&
		                  forward_star_model(g, edge_count,
		                    head_values, to_values, weight_values, next_values) &&
		                  IntArray::full(head, vertex_count, head_values) *
	                  IntArray::full(to, edge_count, to_values) *
		                  IntArray::full(weight, edge_count, weight_values) *
		                  IntArray::full(next, edge_count, next_values) *
		                  IntArray::full(dist, MAX_VERTEX_COUNT, dist_after) *
		                  store_heap(pointer_offset(queue_key, 0, sizeof(int), int), pointer_offset(queue_data, 0, sizeof(int), int), queue_set_before, queue_size)
            */
            /*@ Given queue_set_before */
	            push(queue_key, queue_data, queue_size, neighbor, candidate)
	              /*@ where S_before = queue_set_before */;
	            queue_size = queue_size + 1;
		    }
		  }
		}
	    }
	  }
	  /*@ Assert
	      exists visited_out dist_out queue_set_out,
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
	        dijkstra_heap_loop_state(g, source, visited_out, dist_out, queue_set_out) &&
	        dijkstra_heap_loop_refines(g, source,
	          head_values, to_values, weight_values, next_values,
	          visited_out, dist_out, queue_set_out, X) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        safeExec(graph_state_model(g, visited_out, dist_out), return(tt), X) &&
	        IntArray::full(head, vertex_count, head_values) *
	        IntArray::full(to, edge_count, to_values) *
	        IntArray::full(weight, edge_count, weight_values) *
	        IntArray::full(next, edge_count, next_values) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_out) *
	        IntArray::undef_full(queue_key, MAX_PRIORITY_QUEUE_SIZE) *
	        IntArray::undef_full(queue_data, MAX_PRIORITY_QUEUE_SIZE)
	   */
	}
