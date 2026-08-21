#include "safeexec_def.h"
#include "int_array_def.h"

#define MAX_VERTEX_COUNT 10
#define INF 1000000000
#define MAX_PRIORITY_QUEUE_SIZE 200005

/*@ Import Coq Require Import Algorithms.Dijkstra.Dijkstra */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_lib */
/*@ Import Coq Import DijkstraGraph */
/*@ Import Coq Import DijkstraLinkedForwardStar */

/*@ Extern Coq (G :: *) */
/*@ Extern Coq (state :: *) */
/*@ Extern Coq
      (dijkstra_program : G -> Z -> program state unit)
      (initial_state : Z -> state)
      (dijkstra_init_dist : Z -> Z -> list Z -> Prop)
      (dijkstra_shortest_dist : G -> Z -> list Z -> Prop)
      (dijkstra_nonnegative_edges : G -> Prop)
      (dijkstra_no_overflow : G -> Z -> Prop)
      (dist_init_loop : Z -> list Z -> Prop)
	      (dist_model : list Z -> state -> Prop)
	      (graph_dist_model : G -> list Z -> state -> Prop)
	      (graph_state_model : G -> (Z -> Prop) -> list Z -> state -> Prop)
	      (visited_set_empty : (Z -> Prop) -> Prop)
	      (visited_set_add : (Z -> Prop) -> Z -> (Z -> Prop) -> Prop)
	      (dijkstra_lfs_initial_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_loop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> list (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_after_pop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> list (Z * Z) -> Z -> Z ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_edge_loop_refines :
	        G -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> list (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_after_relax_refines :
	        G -> Z -> Z -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> list (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
      (vector_shape : list Z -> Prop)
      (dist_values_safe : list Z -> Prop)
      (graph_has_size : G -> Z -> Prop)
      (vertex_valid : G -> Z -> Prop)
      (forward_star_model :
        G -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (storage_index : Z -> Prop)
      (edge_index : Z -> Z -> Prop)
      (graph_rep :
        Z -> Z -> Z -> Z -> G -> Z ->
        list Z -> list Z -> list Z -> list Z -> Assertion)
      (dist_rep : Z -> list Z -> Assertion)
      (priority_queue_model :
        list Z -> list Z -> Z -> list (Z * Z) -> Prop)
      (priority_queue_push_result :
        list (Z * Z) -> list (Z * Z) -> Z -> Z -> Prop)
      (priority_queue_pop_result :
        list (Z * Z) -> list (Z * Z) -> Z -> Z -> Prop)
      (priority_queue_push_loop :
        list Z -> list Z -> Z -> Z -> list (Z * Z) -> Prop)
      (priority_queue_pop_loop :
        list Z -> list Z -> Z -> Z -> list (Z * Z) -> Prop)
	      (dijkstra_loop_state :
	        G -> Z -> (Z -> Prop) -> list Z -> list (Z * Z) -> Prop)
	      (dijkstra_edge_loop_state :
	        G -> Z -> (Z -> Prop) -> Z -> Z -> Z ->
	        list Z -> list (Z * Z) -> Prop)
      (eq : {A} -> A -> A -> Prop)
 */

extern int priority_queue_vertex[MAX_PRIORITY_QUEUE_SIZE];
extern int priority_queue_distance[MAX_PRIORITY_QUEUE_SIZE];
extern int priority_queue_size;

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

void priority_queue_clear()
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items : list (Z * Z))
    Require
      priority_queue_model(vertices, distances, size, items) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
    Ensure
      exists vertices1 distances1,
        priority_queue_model(vertices1, distances1, 0, nil) &&
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances1) *
        store(&(priority_queue_size), int, 0)
 */
;

int priority_queue_empty()
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items : list (Z * Z))
    Require
      priority_queue_model(vertices, distances, size, items) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
    Ensure
      priority_queue_model(vertices, distances, size, items) &&
      ((__return == 1 && size == 0) || (__return == 0 && size != 0)) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
 */
;

void priority_queue_push(int vertex, int distance)
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items items_out : list (Z * Z))
    Require
      0 <= size &&
      0 <= vertex && vertex < MAX_VERTEX_COUNT &&
      0 <= distance && distance <= INF &&
      priority_queue_model(vertices, distances, size, items) &&
      priority_queue_push_result(items, items_out, vertex, distance) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
    Ensure
      exists vertices1 distances1,
        priority_queue_model(vertices1, distances1, size + 1, items_out) &&
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances1) *
        store(&(priority_queue_size), int, size + 1)
 */
;

void priority_queue_pop(int *vertex_out, int *distance_out)
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items items_out : list (Z * Z))
         (vertex distance : Z)
    Require
      0 < size && size <= MAX_PRIORITY_QUEUE_SIZE &&
      priority_queue_model(vertices, distances, size, items) &&
      priority_queue_pop_result(items, items_out, vertex, distance) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size) *
      has_int_permission(vertex_out) *
      has_int_permission(distance_out)
    Ensure
      exists vertices1 distances1,
        *vertex_out == vertex &&
        *distance_out == distance &&
        priority_queue_model(vertices1, distances1, size - 1, items_out) &&
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances1) *
        store(&(priority_queue_size), int, size - 1)
 */
;

void dijkstra_linked_forward_star(int vertex_count, int source, int edge_count,
                                  int *head, int *to, int *weight, int *next,
                                  int *dist)
/*@ high_level_spec <= low_level_spec
    With (g : G) (head_values to_values weight_values next_values : list Z)
         (dist0 queue_vertices0 queue_distances0 : list Z)
         (queue_size0 : Z) (queue_items0 : list (Z * Z))
    Require
      graph_has_size(g, vertex_count) &&
      vertex_valid(g, source) &&
      dijkstra_nonnegative_edges(g) &&
      dijkstra_no_overflow(g, source) &&
      0 <= edge_count && edge_count <= MAX_PRIORITY_QUEUE_SIZE &&
	      forward_star_model(g, edge_count,
	        head_values, to_values, weight_values, next_values) &&
	      vector_shape(dist0) &&
	      priority_queue_model(
        queue_vertices0, queue_distances0, queue_size0, queue_items0) &&
      IntArray::full(head, vertex_count, head_values) *
      IntArray::full(to, edge_count, to_values) *
      IntArray::full(weight, edge_count, weight_values) *
      IntArray::full(next, edge_count, next_values) *
      IntArray::full(dist, MAX_VERTEX_COUNT, dist0) *
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
        queue_vertices0) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
        queue_distances0) *
      store(&(priority_queue_size), int, queue_size0)
    Ensure
      exists dist_out queue_vertices1 queue_distances1
             queue_size1 queue_items1,
        dijkstra_shortest_dist(g, source, dist_out) &&
        priority_queue_model(
          queue_vertices1, queue_distances1, queue_size1, queue_items1) &&
        IntArray::full(head, vertex_count, head_values) *
        IntArray::full(to, edge_count, to_values) *
        IntArray::full(weight, edge_count, weight_values) *
        IntArray::full(next, edge_count, next_values) *
        IntArray::full(dist, MAX_VERTEX_COUNT, dist_out) *
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
          queue_vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
          queue_distances1) *
        store(&(priority_queue_size), int, queue_size1)
 */
;

void dijkstra_linked_forward_star(int vertex_count, int source, int edge_count,
                                  int *head, int *to, int *weight, int *next,
                                  int *dist)
/*@ low_level_spec
    With (g : G) (head_values to_values weight_values next_values : list Z)
         (dist0 queue_vertices0 queue_distances0 : list Z)
         (queue_size0 : Z) (queue_items0 : list (Z * Z)) X
    Require
      graph_has_size(g, vertex_count) &&
      vertex_valid(g, source) &&
      dijkstra_nonnegative_edges(g) &&
      0 <= edge_count && edge_count <= MAX_PRIORITY_QUEUE_SIZE &&
      forward_star_model(g, edge_count,
        head_values, to_values, weight_values, next_values) &&
	      dijkstra_lfs_initial_refines(g, source,
	        head_values, to_values, weight_values, next_values, X) &&
	      vector_shape(dist0) &&
	      priority_queue_model(
        queue_vertices0, queue_distances0, queue_size0, queue_items0) &&
      IntArray::full(head, vertex_count, head_values) *
      IntArray::full(to, edge_count, to_values) *
      IntArray::full(weight, edge_count, weight_values) *
      IntArray::full(next, edge_count, next_values) *
      IntArray::full(dist, MAX_VERTEX_COUNT, dist0) *
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
        queue_vertices0) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
        queue_distances0) *
      store(&(priority_queue_size), int, queue_size0)
	    Ensure
	      exists visited_out dist_out queue_vertices1 queue_distances1
	             queue_size1 queue_items1,
	        safeExec(graph_state_model(g, visited_out, dist_out), return(tt), X) &&
	        priority_queue_model(
	          queue_vertices1, queue_distances1, queue_size1, queue_items1) &&
        IntArray::full(head, vertex_count, head_values) *
        IntArray::full(to, edge_count, to_values) *
        IntArray::full(weight, edge_count, weight_values) *
        IntArray::full(next, edge_count, next_values) *
        IntArray::full(dist, MAX_VERTEX_COUNT, dist_out) *
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
          queue_vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
          queue_distances1) *
        store(&(priority_queue_size), int, queue_size1)
 */
{
  dijkstra_linked_forward_star_init(vertex_count, source, dist);

  /*@ Assert
      exists dist_init queue_vertices0 queue_distances0
             queue_size0 queue_items0,
        vertex_count == vertex_count@pre && source == source@pre &&
        edge_count == edge_count@pre &&
        head == head@pre && to == to@pre &&
        weight == weight@pre && next == next@pre && dist == dist@pre &&
        graph_has_size(g, vertex_count) &&
        vertex_valid(g, source) &&
        dijkstra_nonnegative_edges(g) &&
        forward_star_model(g, edge_count,
          head_values, to_values, weight_values, next_values) &&
        dijkstra_init_dist(vertex_count, source, dist_init) &&
        dijkstra_lfs_initial_refines(g, source,
          head_values, to_values, weight_values, next_values, X) &&
        priority_queue_model(
          queue_vertices0, queue_distances0, queue_size0, queue_items0) &&
        IntArray::full(head, vertex_count, head_values) *
        IntArray::full(to, edge_count, to_values) *
        IntArray::full(weight, edge_count, weight_values) *
        IntArray::full(next, edge_count, next_values) *
        IntArray::full(dist, MAX_VERTEX_COUNT, dist_init) *
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
          queue_vertices0) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
          queue_distances0) *
        store(&(priority_queue_size), int, queue_size0)
   */
  priority_queue_clear();

	  /*@ Assert
	      exists visited_init dist_init queue_vertices queue_distances queue_items_initial_after,
	        vertex_count == vertex_count@pre && source == source@pre &&
        edge_count == edge_count@pre &&
        head == head@pre && to == to@pre &&
        weight == weight@pre && next == next@pre && dist == dist@pre &&
        graph_has_size(g, vertex_count) &&
        vertex_valid(g, source) &&
        dijkstra_nonnegative_edges(g) &&
        forward_star_model(g, edge_count,
          head_values, to_values, weight_values, next_values) &&
        dijkstra_init_dist(vertex_count, source, dist_init) &&
	        dijkstra_lfs_initial_refines(g, source,
	          head_values, to_values, weight_values, next_values, X) &&
	        visited_set_empty(visited_init) &&
	        priority_queue_model(queue_vertices, queue_distances, 0, nil) &&
	        priority_queue_push_result(nil, queue_items_initial_after, source, 0) &&
        IntArray::full(head, vertex_count, head_values) *
        IntArray::full(to, edge_count, to_values) *
        IntArray::full(weight, edge_count, weight_values) *
        IntArray::full(next, edge_count, next_values) *
        IntArray::full(dist, MAX_VERTEX_COUNT, dist_init) *
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
          queue_vertices) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
          queue_distances) *
        store(&(priority_queue_size), int, 0)
   */
  /*@ Given queue_items_initial_after */
  priority_queue_push(source, 0)
    /*@ where
          items = nil,
          items_out = queue_items_initial_after */;

	  /*@ Inv Assert
	      exists visited_cur dist_cur queue_vertices queue_distances queue_items,
	        vertex_count == vertex_count@pre && source == source@pre &&
        edge_count == edge_count@pre &&
        head == head@pre && to == to@pre &&
        weight == weight@pre && next == next@pre && dist == dist@pre &&
        graph_has_size(g, vertex_count) &&
        vertex_valid(g, source) &&
        dijkstra_nonnegative_edges(g) &&
	        forward_star_model(g, edge_count,
	          head_values, to_values, weight_values, next_values) &&
	        dijkstra_loop_state(g, source, visited_cur, dist_cur, queue_items) &&
	        dijkstra_loop_refines(g, source,
	          head_values, to_values, weight_values, next_values,
	          visited_cur, dist_cur, queue_items, X) &&
        IntArray::full(head, vertex_count, head_values) *
        IntArray::full(to, edge_count, to_values) *
        IntArray::full(weight, edge_count, weight_values) *
        IntArray::full(next, edge_count, next_values) *
        IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
          queue_vertices) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
          queue_distances) *
        store(&(priority_queue_size), int, Zlength(queue_items)) &&
        priority_queue_model(
          queue_vertices, queue_distances, Zlength(queue_items), queue_items)
   */
  while (!priority_queue_empty()) {
    int cur_vertex;
    int cur_distance;
	    /*@ Assert
	        exists visited_cur dist_cur queue_vertices queue_distances queue_items
	               queue_items_after pop_vertex pop_distance,
          vertex_count == vertex_count@pre && source == source@pre &&
          edge_count == edge_count@pre &&
          head == head@pre && to == to@pre &&
          weight == weight@pre && next == next@pre && dist == dist@pre &&
          graph_has_size(g, vertex_count) &&
          vertex_valid(g, source) &&
          dijkstra_nonnegative_edges(g) &&
	          forward_star_model(g, edge_count,
	            head_values, to_values, weight_values, next_values) &&
	          dijkstra_loop_state(g, source, visited_cur, dist_cur, queue_items) &&
	          dijkstra_loop_refines(g, source,
	            head_values, to_values, weight_values, next_values,
	            visited_cur, dist_cur, queue_items, X) &&
          priority_queue_pop_result(
            queue_items, queue_items_after, pop_vertex, pop_distance) &&
          priority_queue_model(
            queue_vertices, queue_distances,
            Zlength(queue_items), queue_items) &&
          IntArray::full(head, vertex_count, head_values) *
          IntArray::full(to, edge_count, to_values) *
          IntArray::full(weight, edge_count, weight_values) *
          IntArray::full(next, edge_count, next_values) *
          IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
          IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
            queue_vertices) *
          IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
            queue_distances) *
          store(&(priority_queue_size), int, Zlength(queue_items)) *
          has_int_permission(&cur_vertex) *
          has_int_permission(&cur_distance)
     */
    /*@ Given queue_items queue_items_after pop_vertex pop_distance */
    priority_queue_pop(&cur_vertex, &cur_distance)
      /*@ where
            items = queue_items,
            items_out = queue_items_after,
            vertex = pop_vertex,
            distance = pop_distance */;

	    /*@ Assert
	        exists visited_cur dist_cur queue_vertices queue_distances queue_items,
	          vertex_count == vertex_count@pre && source == source@pre &&
          edge_count == edge_count@pre &&
          head == head@pre && to == to@pre &&
          weight == weight@pre && next == next@pre && dist == dist@pre &&
          graph_has_size(g, vertex_count) &&
          vertex_valid(g, source) &&
          dijkstra_nonnegative_edges(g) &&
	          forward_star_model(g, edge_count,
	            head_values, to_values, weight_values, next_values) &&
	          dijkstra_loop_state(g, source, visited_cur, dist_cur, queue_items) &&
	          storage_index(cur_vertex) &&
          0 <= cur_vertex && cur_vertex < vertex_count &&
          cur_vertex < MAX_VERTEX_COUNT &&
          0 <= cur_distance && cur_distance <= INF &&
	          dijkstra_after_pop_refines(g, source,
	            head_values, to_values, weight_values, next_values,
	            visited_cur, dist_cur, queue_items, cur_vertex, cur_distance, X) &&
          IntArray::full(head, vertex_count, head_values) *
          IntArray::full(to, edge_count, to_values) *
          IntArray::full(weight, edge_count, weight_values) *
          IntArray::full(next, edge_count, next_values) *
          IntArray::full(dist, MAX_VERTEX_COUNT, dist_cur) *
          IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
            queue_vertices) *
          IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
            queue_distances) *
          store(&(priority_queue_size), int, Zlength(queue_items)) &&
          priority_queue_model(
            queue_vertices, queue_distances,
            Zlength(queue_items), queue_items)
     */

    if (cur_distance == dist[cur_vertex]) {
	      /*@ Inv Assert
	          exists visited_cur visited_edge dist_edge
	                 queue_vertices queue_distances queue_items,
	            vertex_count == vertex_count@pre && source == source@pre &&
            edge_count == edge_count@pre &&
            head == head@pre && to == to@pre &&
            weight == weight@pre && next == next@pre && dist == dist@pre &&
            graph_has_size(g, vertex_count) &&
            vertex_valid(g, source) &&
            dijkstra_nonnegative_edges(g) &&
            forward_star_model(g, edge_count,
              head_values, to_values, weight_values, next_values) &&
	            0 <= cur_vertex && cur_vertex < vertex_count &&
	            0 <= cur_distance && cur_distance <= INF &&
	            visited_set_add(visited_cur, cur_vertex, visited_edge) &&
	            dijkstra_edge_loop_state(
	              g, source, visited_edge, cur_vertex, cur_distance, edge,
	              dist_edge, queue_items) &&
            (edge == -1 || (0 <= edge && edge < edge_count)) &&
	            dijkstra_edge_loop_refines(g, source, cur_vertex,
	              cur_distance, edge, head_values, to_values, weight_values,
	              next_values, visited_edge, dist_edge, queue_items, X) &&
            IntArray::full(head, vertex_count, head_values) *
            IntArray::full(to, edge_count, to_values) *
            IntArray::full(weight, edge_count, weight_values) *
            IntArray::full(next, edge_count, next_values) *
            IntArray::full(dist, MAX_VERTEX_COUNT, dist_edge) *
            IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
              queue_vertices) *
            IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
              queue_distances) *
            store(&(priority_queue_size), int, Zlength(queue_items)) &&
            priority_queue_model(
              queue_vertices, queue_distances,
              Zlength(queue_items), queue_items)
       */
      for (int edge = head[cur_vertex]; edge != -1; edge = next[edge]) {
        int neighbor = to[edge];
        int edge_weight = weight[edge];

	        /*@ Assert
	            exists visited_cur visited_edge dist_edge
	                   queue_vertices queue_distances queue_items,
	              vertex_count == vertex_count@pre && source == source@pre &&
              edge_count == edge_count@pre &&
              head == head@pre && to == to@pre &&
              weight == weight@pre && next == next@pre && dist == dist@pre &&
              graph_has_size(g, vertex_count) &&
              vertex_valid(g, source) &&
              dijkstra_nonnegative_edges(g) &&
              forward_star_model(g, edge_count,
                head_values, to_values, weight_values, next_values) &&
              0 <= cur_vertex && cur_vertex < vertex_count &&
              0 <= cur_distance && cur_distance <= INF &&
              0 <= edge && edge < edge_count &&
              neighbor == Znth(edge, to_values, 0) &&
              edge_weight == Znth(edge, weight_values, 0) &&
	              0 <= neighbor && neighbor < vertex_count &&
	              neighbor < MAX_VERTEX_COUNT &&
	              0 <= edge_weight && edge_weight <= INF &&
	              visited_set_add(visited_cur, cur_vertex, visited_edge) &&
	              dijkstra_edge_loop_state(
	                g, source, visited_edge, cur_vertex, cur_distance, edge,
	                dist_edge, queue_items) &&
	              dijkstra_edge_loop_refines(g, source, cur_vertex,
	                cur_distance, edge, head_values, to_values, weight_values,
	                next_values, visited_edge, dist_edge, queue_items, X) &&
              IntArray::full(head, vertex_count, head_values) *
              IntArray::full(to, edge_count, to_values) *
              IntArray::full(weight, edge_count, weight_values) *
              IntArray::full(next, edge_count, next_values) *
              IntArray::full(dist, MAX_VERTEX_COUNT, dist_edge) *
              IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
                queue_vertices) *
              IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
                queue_distances) *
              store(&(priority_queue_size), int, Zlength(queue_items)) &&
              priority_queue_model(
                queue_vertices, queue_distances,
                Zlength(queue_items), queue_items)
         */

        if (edge_weight >= 0 && cur_distance <= INF - edge_weight) {
          int candidate = cur_distance + edge_weight;

          if (candidate < dist[neighbor]) {
            dist[neighbor] = candidate;
	            /*@ Assert
	                exists visited_cur visited_edge dist_after
	                       queue_vertices queue_distances
	                       queue_items_before push_items_after,
                  vertex_count == vertex_count@pre &&
                  source == source@pre &&
                  edge_count == edge_count@pre &&
                  head == head@pre && to == to@pre &&
                  weight == weight@pre && next == next@pre &&
                  dist == dist@pre &&
                  graph_has_size(g, vertex_count) &&
                  vertex_valid(g, source) &&
                  dijkstra_nonnegative_edges(g) &&
                  forward_star_model(g, edge_count,
                    head_values, to_values, weight_values, next_values) &&
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
	                  dijkstra_edge_loop_state(
	                    g, source, visited_edge, cur_vertex, cur_distance, edge,
	                    dist_after, queue_items_before) &&
	                  dijkstra_after_relax_refines(g, source, cur_vertex,
	                    cur_distance, edge, neighbor, candidate, head_values,
	                    to_values, weight_values, next_values,
	                    visited_edge, dist_after, queue_items_before, X) &&
                  priority_queue_push_result(
                    queue_items_before, push_items_after, neighbor, candidate) &&
                  priority_queue_model(
                    queue_vertices, queue_distances,
                    Zlength(queue_items_before), queue_items_before) &&
                  IntArray::full(head, vertex_count, head_values) *
                  IntArray::full(to, edge_count, to_values) *
                  IntArray::full(weight, edge_count, weight_values) *
                  IntArray::full(next, edge_count, next_values) *
                  IntArray::full(dist, MAX_VERTEX_COUNT, dist_after) *
                  IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
                    queue_vertices) *
                  IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
                    queue_distances) *
                  store(&(priority_queue_size), int, Zlength(queue_items_before))
            */
            /*@ Given queue_items_before push_items_after */
            priority_queue_push(neighbor, candidate)
              /*@ where
                    items = queue_items_before,
                    items_out = push_items_after */;
          }
        }
      }
    }
  }
}
