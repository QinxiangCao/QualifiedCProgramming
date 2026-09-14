#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "safeexec_def.h"
#include "Data_structures/priority_queue_decrease_key/priority_queue_decrease_key_def.h"

#define MAX_PRIORITY_QUEUE_SIZE 100000
#define INF 1000000000

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Prim.prim_forward_star_heap_lib */
/*@ Import Coq From ListLib.Base Require Import Positional */
/*@ Extern Coq (St :: *) */
/*@ Extern Coq (E :: *) */
/*@ Extern Coq V := Z */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq (Prim2: G -> program St unit) */
/*@ Extern Coq (Prim2_loop: G -> Z -> program St unit) */
/*@ Extern Coq (initSt: G -> V -> St) */
/*@ Extern Coq (initStPred: G -> V -> St -> Prop) */
/*@ Extern Coq (PrimEnv: G -> V -> Prop) */
/*@ Extern Coq (array_graph: Z -> Z -> list Z -> list Z -> list Z -> G -> Prop) */
/*@ Extern Coq (directed_array_graph: G -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (directed_array_graph_prefix: Z -> G -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (prim_state_is: St -> St -> Prop) */
/*@ Extern Coq (prim_state_graph_matches: G -> St -> Prop) */
/*@ Extern Coq (return_is_mst: G -> G -> Prop) */
/*@ Extern Coq (prim_result_graph_matches_array: Z -> list Z -> list Z -> list Z -> G -> G -> Prop) */
/*@ Extern Coq (prim_result_graph_matches_array_prefix: Z -> Z -> list Z -> list Z -> list Z -> G -> G -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (first_link_matches_inserted_vertex_directed_edges: G -> Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (first_link_matches_vertex_directed_edges: G -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (growing_subgraph_state: G -> St -> Prop) */
/*@ Extern Coq (visited_matches_state: G -> St -> list Z -> Prop) */
/*@ Extern Coq (state_vertex_count: St -> Z) */
/*@ Extern Coq (selected_edges_match_state: G -> V -> St -> list Z -> Prop) */
/*@ Extern Coq (lowcost_parent_match: G -> St -> list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (candidate_vertex_exists_in_range: Z -> G -> St -> list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (min_vertex_in_range: G -> St -> Z -> Z -> V -> list Z -> list Z -> Prop) */
/*@ Extern Coq (selected_parent_edge_is_min_cut_edge: G -> St -> list Z -> V -> Prop) */
/*@ Extern Coq (selected_parent_pair: G -> St -> list Z -> list Z -> list Z -> V -> V -> V -> Prop) */
/*@ Extern Coq (selected_parent_add_to_mst: G -> St -> St -> list Z -> list Z -> list Z -> V -> Prop) */
/*@ Extern Coq (selected_state_after_add: G -> V -> Z -> Z -> St -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> Prop) */
/*@ Extern Coq (scan_one_directed_edge_update: G -> St -> list Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_update: G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_prefix_update: G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> Z -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (partial_map_empty: partial_map) */
/*@ Extern Coq (prim_queue_map_initial: partial_map -> partial_map -> V -> Z -> Prop) */
/*@ Extern Coq (prim_queue_map_pop: partial_map -> partial_map -> V -> Z -> Prop) */
/*@ Extern Coq (prim_queue_map_update_or_push:
      partial_map -> partial_map -> Z -> Z -> V -> Z -> Prop) */
/*@ Extern Coq (prim_heap_map_matches_state:
      G -> St -> list Z -> list Z -> Z -> partial_map -> Prop) */
/*@ Extern Coq (prim_heap_map_matches_state_by:
      G -> St -> (V -> E -> Prop) -> list Z -> list Z -> Z -> partial_map -> Prop) */
/*@ Extern Coq (prim_heap_map_pop_selects_min_vertex:
      G -> St -> list Z -> list Z -> Z -> partial_map -> Z -> V -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_map_prefix_update:
      G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> Z ->
      list Z -> list Z -> partial_map -> list Z -> list Z -> partial_map -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_map_update:
      G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V ->
      list Z -> list Z -> partial_map -> list Z -> list Z -> partial_map -> Prop) */
/*@ Extern Coq (prim_heap_loop_state:
      G -> V -> Z -> St -> list Z -> list Z -> list Z -> partial_map ->
      (unit -> St -> Prop) -> Prop) */
/*@ Extern Coq (prim_heap_after_pop_state:
      G -> V -> Z -> St -> list Z -> list Z -> list Z ->
      partial_map -> partial_map -> V -> Z -> (unit -> St -> Prop) -> Prop) */
/*@ Extern Coq (prim_heap_scan_state:
      G -> V -> Z -> St -> St ->
      list Z -> list Z -> list Z -> list Z -> list Z ->
      list Z -> list Z -> list Z ->
      list Z -> list Z -> Z -> V -> Z -> partial_map ->
      list Z -> list Z -> partial_map -> (unit -> St -> Prop) -> Prop) */
/*@ Extern Coq (prim_heap_done_state:
      G -> V -> St -> list Z -> list Z -> list Z -> partial_map ->
      (unit -> St -> Prop) -> Prop) */

struct mst_tree {
	int* u;
	int* v;
	int* wt;
};

int* malloc_int_array(int n)
/*@ Require n > 0 && emp
	Ensure IntArray::undef_full(__return, n)
*/
;

struct mst_tree* malloc_mst_tree()
/*@ Require emp
	Ensure __return != 0 &&
		has_permission(&(__return -> u)) *
		has_permission(&(__return -> v)) *
		has_permission(&(__return -> wt))
*/
;


struct mst_tree* prim_forward_star_heap(int* from_arr, int* to_arr,
										int* weight_arr, int n, int m)
/*@ high_level_spec <= low_level_spec
	With (lf: list Z) (lt: list Z) (lw: list Z) (g : G) (src: V)
	Require
		src == 0 &&
		2 <= n && n < INT_MAX &&
		1 <= m && 2 * m + 2 < INT_MAX && 4 * m + 6 < INT_MAX &&
		2 * m + 2 <= 100000 &&
		(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n) &&
		(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n) &&
		(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
		array_graph(n, m, lf, lt, lw, g) &&
		PrimEnv(g, src) &&

		IntArray::full(from_arr, m, lf) *
		IntArray::full(to_arr, m, lt) *
		IntArray::full(weight_arr, m, lw)
		Ensure
			exists lru lrv lrwt rg
			       r_from_new r_to_new r_weight_new r_first r_link
			       r_lowcost r_visited r_edge_parent r_heap_cost r_heap_vertex r_heap_pos
			       r_heap_size r_queue_map
			       l_from_new_ret l_to_new_ret l_weight_new_ret l_first_ret l_link_ret
			       l_lowcost_ret l_visited_ret l_edge_parent_ret,
				return_is_mst(g, rg) &&
				prim_result_graph_matches_array(n, lru, lrv, lrwt, g, rg) &&
				__return != 0 &&

				IntArray::full(__return -> u, n - 1, lru) *
				IntArray::full(__return -> v, n - 1, lrv) *
				IntArray::full(__return -> wt, n - 1, lrwt) *
				IntArray::full(from_arr, m, lf) *
				IntArray::full(to_arr, m, lt) *
				IntArray::full(weight_arr, m, lw) *
				IntArray::full(r_from_new, 2 * m, l_from_new_ret) *
				IntArray::full(r_to_new, 2 * m, l_to_new_ret) *
				IntArray::full(r_weight_new, 2 * m, l_weight_new_ret) *
				IntArray::full(r_first, n, l_first_ret) *
				IntArray::full(r_link, 2 * m, l_link_ret) *
				IntArray::full(r_lowcost, n, l_lowcost_ret) *
				IntArray::full(r_visited, n, l_visited_ret) *
				IntArray::full(r_edge_parent, n, l_edge_parent_ret) *
				store_heap(r_heap_cost, r_heap_vertex, r_heap_pos,
					n, 2 * m + 2, r_queue_map, r_heap_size)
*/
;

struct mst_tree* prim_forward_star_heap(int* from_arr, int* to_arr,
										int* weight_arr, int n, int m)
/*@ low_level_spec
	With (lf: list Z) (lt: list Z) (lw: list Z) (g : G) (src: V) X
	Require
		src == 0 &&
		2 <= n && n < INT_MAX &&
		1 <= m && 2 * m + 2 < INT_MAX && 4 * m + 6 < INT_MAX &&
		2 * m + 2 <= 100000 &&
		(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n) &&
		(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n) &&
		(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
		array_graph(n, m, lf, lt, lw, g) &&
		PrimEnv(g, src) &&

		IntArray::full(from_arr, m, lf) *
		IntArray::full(to_arr, m, lt) *
		IntArray::full(weight_arr, m, lw) *
		safeExec(initStPred(g, src), Prim2(g), X)
	Ensure
		exists lru lrv lrwt rg
		       r_from_new r_to_new r_weight_new r_first r_link
		       r_lowcost r_visited r_edge_parent r_heap_cost r_heap_vertex r_heap_pos
		       r_heap_size r_queue_map
		       l_from_new_ret l_to_new_ret l_weight_new_ret l_first_ret l_link_ret
		       l_lowcost_ret l_visited_ret l_edge_parent_ret,
			safeExec(prim_state_graph_matches(rg), return(tt), X) &&
			prim_result_graph_matches_array(n, lru, lrv, lrwt, g, rg) &&
			__return != 0 &&

			IntArray::full(__return -> u, n - 1, lru) *
			IntArray::full(__return -> v, n - 1, lrv) *
			IntArray::full(__return -> wt, n - 1, lrwt) *
			IntArray::full(from_arr, m, lf) *
			IntArray::full(to_arr, m, lt) *
			IntArray::full(weight_arr, m, lw) *
			IntArray::full(r_from_new, 2 * m, l_from_new_ret) *
			IntArray::full(r_to_new, 2 * m, l_to_new_ret) *
			IntArray::full(r_weight_new, 2 * m, l_weight_new_ret) *
			IntArray::full(r_first, n, l_first_ret) *
			IntArray::full(r_link, 2 * m, l_link_ret) *
			IntArray::full(r_lowcost, n, l_lowcost_ret) *
			IntArray::full(r_visited, n, l_visited_ret) *
			IntArray::full(r_edge_parent, n, l_edge_parent_ret) *
			store_heap(r_heap_cost, r_heap_vertex, r_heap_pos,
				n, 2 * m + 2, r_queue_map, r_heap_size)
*/
{
	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_wt = malloc_int_array(n - 1);

	int* from_new = malloc_int_array(2 * m);
	int* to_new = malloc_int_array(2 * m);
	int* weight_new = malloc_int_array(2 * m);

	{
	int i = 0;
	/*@ Inv Assert
		exists l_from_new_prefix l_to_new_prefix l_weight_new_prefix,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
			n == n@pre && m == m@pre &&
			from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
			0 <= i && i <= m@pre &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n@pre, m@pre, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			directed_array_graph_prefix(i, g,
				l_from_new_prefix, l_to_new_prefix, l_weight_new_prefix) &&

			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			IntArray::undef_full(out_u, n@pre - 1) *
			IntArray::undef_full(out_v, n@pre - 1) *
			IntArray::undef_full(out_wt, n@pre - 1) *
			IntArray::seg(from_new, 0, 2 * i, l_from_new_prefix) *
			IntArray::undef_seg(from_new, 2 * i, 2 * m@pre) *
			IntArray::seg(to_new, 0, 2 * i, l_to_new_prefix) *
			IntArray::undef_seg(to_new, 2 * i, 2 * m@pre) *
			IntArray::seg(weight_new, 0, 2 * i, l_weight_new_prefix) *
			IntArray::undef_seg(weight_new, 2 * i, 2 * m@pre)
	*/
	for (; i < m; i++) {
		from_new[2 * i] = from_arr[i];
		to_new[2 * i] = to_arr[i];
		weight_new[2 * i] = weight_arr[i];

		from_new[2 * i + 1] = to_arr[i];
		to_new[2 * i + 1] = from_arr[i];
		weight_new[2 * i + 1] = weight_arr[i];
	}
	}

	int* first = malloc_int_array(n);
	int* link = malloc_int_array(2 * m);

	{
	int i = 0;
	/*@ Inv Assert
		exists l_from_new l_to_new l_weight_new,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
			n == n@pre && m == m@pre &&
			from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
			0 <= i && i <= n@pre &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n@pre, m@pre, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&

			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			IntArray::undef_full(out_u, n@pre - 1) *
			IntArray::undef_full(out_v, n@pre - 1) *
			IntArray::undef_full(out_wt, n@pre - 1) *
							IntArray::full(from_new, Zlength(l_from_new), l_from_new) *
							IntArray::full(to_new, Zlength(l_to_new), l_to_new) *
							IntArray::full(weight_new, Zlength(l_weight_new), l_weight_new) *
			IntArray::seg(first, 0, i, repeat_Z(-1, i)) *
			IntArray::undef_seg(first, i, n@pre) *
			IntArray::undef_full(link, 2 * m@pre)
	*/
	for (; i < n; i++) {
		first[i] = -1;
	}
	}

	{
	int i = 0;
	/*@ Inv Assert
		exists l_from_new l_to_new l_weight_new,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
			n == n@pre && m == m@pre &&
			from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
			0 <= i && i <= 2 * m@pre &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n@pre, m@pre, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&

			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			IntArray::undef_full(out_u, n@pre - 1) *
			IntArray::undef_full(out_v, n@pre - 1) *
			IntArray::undef_full(out_wt, n@pre - 1) *
			IntArray::full(from_new, 2 * m@pre, l_from_new) *
			IntArray::full(to_new, 2 * m@pre, l_to_new) *
			IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
			IntArray::full(first, n@pre, repeat_Z(-1, n@pre)) *
			IntArray::seg(link, 0, i, repeat_Z(-1, i)) *
			IntArray::undef_seg(link, i, 2 * m@pre)
	*/
	for (; i < 2 * m; i++) {
		link[i] = -1;
	}
	}

	{
	int i = 0;
	/*@ Inv Assert
		exists l_first l_link l_from_new l_to_new l_weight_new,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
			n == n@pre && m == m@pre &&
			from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
			0 <= i && i <= 2 * m@pre &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n@pre, m@pre, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
			first_link_matches_inserted_vertex_directed_edges(g, i, l_from_new, l_first, l_link) &&

			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			IntArray::undef_full(out_u, n@pre - 1) *
			IntArray::undef_full(out_v, n@pre - 1) *
			IntArray::undef_full(out_wt, n@pre - 1) *
			IntArray::full(from_new, 2 * m@pre, l_from_new) *
			IntArray::full(to_new, 2 * m@pre, l_to_new) *
			IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
			IntArray::full(link, 2 * m@pre, l_link)
		*/
			for (; i < 2 * m; i++) {
				int u = from_new[i];
							/*@ Assert
								exists l_first l_link l_from_new l_to_new l_weight_new,
						2 <= n@pre && n@pre < INT_MAX &&
						1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
						2 * m@pre + 2 <= 100000 &&
						src == 0 &&
					n == n@pre && m == m@pre &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
					0 <= i && i < 2 * m@pre &&
					u == Znth(i, l_from_new, 0) &&
					0 <= u && u < n@pre &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
					PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_inserted_vertex_directed_edges(g, i, l_from_new, l_first, l_link) &&

					safeExec(initStPred(g, src), Prim2(g), X) &&

					IntArray::full(from_arr@pre, m@pre, lf) *
					IntArray::full(to_arr@pre, m@pre, lt) *
					IntArray::full(weight_arr@pre, m@pre, lw) *
					IntArray::undef_full(out_u, n@pre - 1) *
					IntArray::undef_full(out_v, n@pre - 1) *
					IntArray::undef_full(out_wt, n@pre - 1) *
							IntArray::full(from_new, Zlength(l_from_new), l_from_new) *
							IntArray::full(to_new, Zlength(l_to_new), l_to_new) *
							IntArray::full(weight_new, Zlength(l_weight_new), l_weight_new) *
						IntArray::full(first, n@pre, l_first) *
					IntArray::full(link, 2 * m@pre, l_link)
			*/
				int tmp = first[u];
				first[u] = i;
				link[i] = tmp;
			}
	}

	int* visited = malloc_int_array(n);
	int* lowcost = malloc_int_array(n);
	int* edge_parent = malloc_int_array(n);

	{
	int i = 0;
	/*@ Inv Assert
									exists l_first l_link l_from_new l_to_new l_weight_new,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
			n == n@pre && m == m@pre &&
			from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
			0 <= i && i <= n@pre &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n@pre, m@pre, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
			first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			IntArray::undef_full(out_u, n@pre - 1) *
			IntArray::undef_full(out_v, n@pre - 1) *
			IntArray::undef_full(out_wt, n@pre - 1) *
			IntArray::full(from_new, 2 * m@pre, l_from_new) *
			IntArray::full(to_new, 2 * m@pre, l_to_new) *
			IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
			IntArray::full(link, 2 * m@pre, l_link) *
			IntArray::seg(lowcost, 0, i, repeat_Z(1000000000, i)) *
			IntArray::undef_seg(lowcost, i, n@pre) *
			IntArray::seg(visited, 0, i, repeat_Z(0, i)) *
			IntArray::undef_seg(visited, i, n@pre) *
			IntArray::seg(edge_parent, 0, i, repeat_Z(-1, i)) *
			IntArray::undef_seg(edge_parent, i, n@pre)
	*/
	for (; i < n; i++) {
		visited[i] = 0;
		lowcost[i] = 1000000000;
		edge_parent[i] = -1;
	}

	/*@ Assert
									exists l_first l_link l_from_new l_to_new l_weight_new,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
			n == n@pre && m == m@pre &&
			from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
			i == n@pre &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
			(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n@pre, m@pre, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
			first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			IntArray::undef_full(out_u, n@pre - 1) *
			IntArray::undef_full(out_v, n@pre - 1) *
			IntArray::undef_full(out_wt, n@pre - 1) *
			IntArray::full(from_new, 2 * m@pre, l_from_new) *
			IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
			IntArray::full(link, 2 * m@pre, l_link) *
			IntArray::full(lowcost, n@pre, repeat_Z(1000000000, n@pre)) *
				IntArray::full(visited, n@pre, repeat_Z(0, n@pre)) *
				IntArray::full(edge_parent, n@pre, repeat_Z(-1, n@pre))
		*/
		}

		int heap_capacity = 2 * m + 2;
		int* heap_cost = malloc_int_array(heap_capacity);
		int* heap_vertex = malloc_int_array(heap_capacity);
		int* heap_pos = malloc_int_array(n);
		int heap_size = 0;

		{
			int pos_i = 0;
			/*@ Inv Assert
				exists l_first l_link l_from_new l_to_new l_weight_new,
					2 <= n@pre && n@pre < INT_MAX &&
					1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
					2 * m@pre + 2 <= 100000 &&
					src == 0 &&
					n == n@pre && m == m@pre &&
					heap_capacity == 2 * m@pre + 2 &&
					heap_size == 0 &&
					0 <= pos_i && pos_i <= n@pre &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
					PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
					safeExec(initStPred(g, src), Prim2(g), X) &&

					IntArray::full(from_arr@pre, m@pre, lf) *
					IntArray::full(to_arr@pre, m@pre, lt) *
					IntArray::full(weight_arr@pre, m@pre, lw) *
					IntArray::undef_full(out_u, n@pre - 1) *
					IntArray::undef_full(out_v, n@pre - 1) *
					IntArray::undef_full(out_wt, n@pre - 1) *
					IntArray::full(from_new, 2 * m@pre, l_from_new) *
					IntArray::full(to_new, 2 * m@pre, l_to_new) *
					IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
					IntArray::full(first, n@pre, l_first) *
					IntArray::full(link, 2 * m@pre, l_link) *
					IntArray::full(lowcost, n@pre, repeat_Z(1000000000, n@pre)) *
					IntArray::full(visited, n@pre, repeat_Z(0, n@pre)) *
					IntArray::full(edge_parent, n@pre, repeat_Z(-1, n@pre)) *
					IntArray::undef_seg(heap_cost, 0, heap_capacity) *
					IntArray::undef_seg(heap_vertex, 0, heap_capacity) *
					IntArray::seg(heap_pos, 0, pos_i, repeat_Z(-1, pos_i)) *
					IntArray::undef_seg(heap_pos, pos_i, n@pre)
			*/
			for (; pos_i < n; pos_i++) {
				heap_pos[pos_i] = -1;
			}
		}

		lowcost[0] = 0;
		/*@ Assert
			exists l_first l_link l_from_new l_to_new l_weight_new queue_map_empty queue_map_initial,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
				n == n@pre && m == m@pre &&
				heap_capacity == 2 * m@pre + 2 &&
				heap_size == 0 &&
				from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
				queue_map_empty == partial_map_empty &&
				partial_map_absent(queue_map_empty, src) &&
				prim_queue_map_initial(queue_map_empty, queue_map_initial, src, 0) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
				array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
				directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
				first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
				safeExec(initStPred(g, src), Prim2(g), X) &&

				IntArray::full(from_arr@pre, m@pre, lf) *
				IntArray::full(to_arr@pre, m@pre, lt) *
				IntArray::full(weight_arr@pre, m@pre, lw) *
				IntArray::undef_full(out_u, n@pre - 1) *
				IntArray::undef_full(out_v, n@pre - 1) *
				IntArray::undef_full(out_wt, n@pre - 1) *
				IntArray::full(from_new, 2 * m@pre, l_from_new) *
				IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
				IntArray::full(link, 2 * m@pre, l_link) *
				IntArray::full(lowcost, n@pre, replace_Znth(0, 0, repeat_Z(1000000000, n@pre))) *
				IntArray::full(visited, n@pre, repeat_Z(0, n@pre)) *
				IntArray::full(edge_parent, n@pre, repeat_Z(-1, n@pre)) *
				store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map_empty, heap_size)
		*/
		/*@ Given queue_map_empty */
		pqdk_push(heap_cost, heap_vertex, heap_pos, &heap_size, n, 0, 0)
			/*@ where M_before = queue_map_empty, n = heap_size, capacity = heap_capacity */;

		int chosen = 0;
		/*@ Assert
			exists l_first l_link l_from_new l_to_new l_weight_new queue_map s,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
				n == n@pre && m == m@pre &&
				heap_capacity == 2 * m@pre + 2 &&
				chosen == 0 && heap_size == 1 &&
				from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
				prim_queue_map_initial(partial_map_empty, queue_map, src, 0) &&
				prim_heap_loop_state(g, src, chosen, s,
					replace_Znth(0, 0, repeat_Z(1000000000, n@pre)),
					repeat_Z(0, n@pre), repeat_Z(-1, n@pre), queue_map, X) &&
				(chosen < n@pre => heap_size > 0) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
				array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
				directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
				first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

				IntArray::full(from_arr@pre, m@pre, lf) *
				IntArray::full(to_arr@pre, m@pre, lt) *
				IntArray::full(weight_arr@pre, m@pre, lw) *
				IntArray::undef_full(out_u, n@pre - 1) *
				IntArray::undef_full(out_v, n@pre - 1) *
				IntArray::undef_full(out_wt, n@pre - 1) *
				IntArray::full(from_new, 2 * m@pre, l_from_new) *
				IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
				IntArray::full(link, 2 * m@pre, l_link) *
				IntArray::full(lowcost, n@pre, replace_Znth(0, 0, repeat_Z(1000000000, n@pre))) *
				IntArray::full(visited, n@pre, repeat_Z(0, n@pre)) *
				IntArray::full(edge_parent, n@pre, repeat_Z(-1, n@pre)) *
				store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
		*/

		/*@ Inv Assert
			exists l_first l_link l_from_new l_to_new l_weight_new
			       l_lowcost l_visited l_edge_parent queue_map s,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
				n == n@pre && m == m@pre &&
				heap_capacity == 2 * m@pre + 2 &&
				0 <= chosen && chosen <= n@pre &&
				0 <= heap_size && heap_size <= heap_capacity &&
				from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
				array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
				directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
				first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
				prim_heap_loop_state(g, src, chosen, s,
					l_lowcost, l_visited, l_edge_parent, queue_map, X) &&
				(chosen < n@pre => heap_size > 0) &&

				IntArray::full(from_arr@pre, m@pre, lf) *
				IntArray::full(to_arr@pre, m@pre, lt) *
				IntArray::full(weight_arr@pre, m@pre, lw) *
				IntArray::undef_full(out_u, n@pre - 1) *
				IntArray::undef_full(out_v, n@pre - 1) *
				IntArray::undef_full(out_wt, n@pre - 1) *
				IntArray::full(from_new, 2 * m@pre, l_from_new) *
				IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
				IntArray::full(link, 2 * m@pre, l_link) *
				IntArray::full(lowcost, n@pre, l_lowcost) *
				IntArray::full(visited, n@pre, l_visited) *
				IntArray::full(edge_parent, n@pre, l_edge_parent) *
				store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
		*/
		while (heap_size > 0 && chosen < n) {
			int minIndex;
			int min;
			/*@ Assert
				exists l_first l_link l_from_new l_to_new l_weight_new
				       l_lowcost l_visited l_edge_parent queue_map s,
					2 <= n@pre && n@pre < INT_MAX &&
					1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
					2 * m@pre + 2 <= 100000 &&
					src == 0 &&
					n == n@pre && m == m@pre &&
					heap_capacity == 2 * m@pre + 2 &&
					0 <= chosen && chosen < n@pre &&
					0 < heap_size && heap_size <= heap_capacity &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
					PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
					prim_heap_loop_state(g, src, chosen, s,
						l_lowcost, l_visited, l_edge_parent, queue_map, X) &&

					IntArray::full(from_arr@pre, m@pre, lf) *
					IntArray::full(to_arr@pre, m@pre, lt) *
					IntArray::full(weight_arr@pre, m@pre, lw) *
					IntArray::undef_full(out_u, n@pre - 1) *
					IntArray::undef_full(out_v, n@pre - 1) *
					IntArray::undef_full(out_wt, n@pre - 1) *
					IntArray::full(from_new, 2 * m@pre, l_from_new) *
					IntArray::full(to_new, 2 * m@pre, l_to_new) *
					IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
					IntArray::full(first, n@pre, l_first) *
					IntArray::full(link, 2 * m@pre, l_link) *
					IntArray::full(lowcost, n@pre, l_lowcost) *
					IntArray::full(visited, n@pre, l_visited) *
					IntArray::full(edge_parent, n@pre, l_edge_parent) *
					store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size) *
					has_int_permission(&minIndex) *
					has_int_permission(&min)
			*/
			/*@ Given queue_map */
			pqdk_pop(heap_cost, heap_vertex, heap_pos, &heap_size, n, &minIndex, &min)
				/*@ where M_before = queue_map, n = heap_size, capacity = heap_capacity */;

			/*@ Assert
				exists l_first l_link l_from_new l_to_new l_weight_new
				       l_lowcost l_visited l_edge_parent queue_map_before queue_map s,
					2 <= n@pre && n@pre < INT_MAX &&
					1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
					2 * m@pre + 2 <= 100000 &&
					src == 0 &&
					n == n@pre && m == m@pre &&
					heap_capacity == 2 * m@pre + 2 &&
					0 <= chosen && chosen < n@pre &&
					0 <= heap_size && heap_size < heap_capacity &&
					0 <= minIndex && minIndex < n@pre &&
					INT_MIN <= min && min <= INT_MAX &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
					prim_heap_loop_state(g, src, chosen, s,
						l_lowcost, l_visited, l_edge_parent, queue_map_before, X) &&
					prim_queue_map_pop(queue_map_before, queue_map, minIndex, min) &&
					prim_heap_after_pop_state(g, src, chosen, s,
						l_lowcost, l_visited, l_edge_parent,
						queue_map_before, queue_map, minIndex, min, X) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
					PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

					IntArray::full(from_arr@pre, m@pre, lf) *
					IntArray::full(to_arr@pre, m@pre, lt) *
					IntArray::full(weight_arr@pre, m@pre, lw) *
					IntArray::undef_full(out_u, n@pre - 1) *
					IntArray::undef_full(out_v, n@pre - 1) *
					IntArray::undef_full(out_wt, n@pre - 1) *
					IntArray::full(from_new, 2 * m@pre, l_from_new) *
					IntArray::full(to_new, 2 * m@pre, l_to_new) *
					IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
					IntArray::missing_i(first, minIndex, 0, n@pre, l_first) *
					data_at(first + (minIndex * sizeof(int)), int, Znth(minIndex, l_first, 0)) *
					IntArray::full(link, 2 * m@pre, l_link) *
					IntArray::full(lowcost, n@pre, l_lowcost) *
					IntArray::missing_i(visited, minIndex, 0, n@pre, l_visited) *
					data_at(visited + (minIndex * sizeof(int)), int, Znth(minIndex, l_visited, 0)) *
					IntArray::full(edge_parent, n@pre, l_edge_parent) *
					store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
			*/
			visited[minIndex] = 1;
			chosen++;
			int cur_edge = first[minIndex];
			/*@ Inv Assert
					exists current_edge selected l_first l_link l_from_new l_to_new l_weight_new
					       l_lowcost l_visited l_edge_parent
					       l_lowcost_cur l_edge_parent_cur queue_map_before queue_map_cur s s_after,
					2 <= n@pre && n@pre < INT_MAX &&
					1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
					2 * m@pre + 2 <= 100000 &&
					src == 0 &&
					n == n@pre && m == m@pre &&
					heap_capacity == 2 * m@pre + 2 &&
					1 <= chosen && chosen <= n@pre &&
					0 <= heap_size && heap_size <= heap_capacity &&
						0 <= selected && selected < n@pre &&
						cur_edge == current_edge &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
						prim_heap_scan_state(g, src, chosen, s, s_after,
							l_from_new, l_first, l_link, l_to_new, l_weight_new,
							l_lowcost, replace_Znth(selected, 1, l_visited), l_edge_parent,
							l_lowcost_cur, l_edge_parent_cur, current_edge, selected, min,
							queue_map_before, l_lowcost_cur, l_edge_parent_cur, queue_map_cur, X) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
					PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

					IntArray::full(from_arr@pre, m@pre, lf) *
					IntArray::full(to_arr@pre, m@pre, lt) *
					IntArray::full(weight_arr@pre, m@pre, lw) *
					IntArray::undef_full(out_u, n@pre - 1) *
					IntArray::undef_full(out_v, n@pre - 1) *
					IntArray::undef_full(out_wt, n@pre - 1) *
					IntArray::full(from_new, 2 * m@pre, l_from_new) *
					IntArray::full(to_new, 2 * m@pre, l_to_new) *
					IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
						IntArray::full(first, n@pre, l_first) *
						IntArray::full(link, 2 * m@pre, l_link) *
							IntArray::full(lowcost, n@pre, l_lowcost_cur) *
							IntArray::full(visited, n@pre, replace_Znth(selected, 1, l_visited)) *
							IntArray::full(edge_parent, n@pre, l_edge_parent_cur) *
							store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map_cur, heap_size) *
							has_permission(&minIndex)
			*/
			while (cur_edge != -1) {
				if (0 <= cur_edge && cur_edge < 2 * m) {
					int to_node = to_new[cur_edge];
					int edge_weight = weight_new[cur_edge];
					if (0 <= to_node && to_node < n && visited[to_node] == 0 && edge_weight < lowcost[to_node]) {
						lowcost[to_node] = edge_weight;
						edge_parent[to_node] = cur_edge;
						/*@ Assert
								exists current_edge selected l_first l_link l_from_new l_to_new l_weight_new
								       l_lowcost l_visited l_edge_parent
								       l_lowcost_cur l_edge_parent_cur l_lowcost_next l_edge_parent_next
							       queue_map_before queue_map_cur s s_after,
								2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
								2 * m@pre + 2 <= 100000 &&
								src == 0 &&
								n == n@pre && m == m@pre &&
								from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
								heap_capacity == 2 * m@pre + 2 &&
									0 <= heap_size && heap_size < heap_capacity &&
									1 <= chosen && chosen <= n@pre &&
										0 <= selected && selected < n@pre &&
									0 <= cur_edge && cur_edge < 2 * m@pre &&
									0 <= to_node && to_node < n@pre &&
									INT_MIN <= edge_weight && edge_weight <= INT_MAX &&
									cur_edge == current_edge &&
									to_node == Znth(cur_edge, l_to_new, 0) &&
									edge_weight == Znth(cur_edge, l_weight_new, 0) &&
									edge_weight < Znth(to_node, l_lowcost_cur, 0) &&
										Znth(to_node, replace_Znth(selected, 1, l_visited), 0) == 0 &&
									l_lowcost_next == replace_Znth(to_node, edge_weight, l_lowcost_cur) &&
									l_edge_parent_next == replace_Znth(to_node, cur_edge, l_edge_parent_cur) &&
								partial_map_update_or_add_pre(queue_map_cur, to_node, edge_weight) &&
									prim_heap_scan_state(g, src, chosen, s, s_after,
										l_from_new, l_first, l_link, l_to_new, l_weight_new,
										l_lowcost, replace_Znth(selected, 1, l_visited), l_edge_parent,
										l_lowcost_cur, l_edge_parent_cur, current_edge, selected, min,
										queue_map_before, l_lowcost_cur, l_edge_parent_cur, queue_map_cur, X) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
								array_graph(n@pre, m@pre, lf, lt, lw, g) &&
								PrimEnv(g, src) &&
								directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
								first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

								IntArray::full(from_arr@pre, m@pre, lf) *
								IntArray::full(to_arr@pre, m@pre, lt) *
								IntArray::full(weight_arr@pre, m@pre, lw) *
								IntArray::undef_full(out_u, n@pre - 1) *
								IntArray::undef_full(out_v, n@pre - 1) *
								IntArray::undef_full(out_wt, n@pre - 1) *
								IntArray::full(from_new, 2 * m@pre, l_from_new) *
								IntArray::full(to_new, 2 * m@pre, l_to_new) *
								IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
									IntArray::full(first, n@pre, l_first) *
									IntArray::full(link, 2 * m@pre, l_link) *
										IntArray::full(lowcost, n@pre, l_lowcost_next) *
										IntArray::full(visited, n@pre, replace_Znth(selected, 1, l_visited)) *
										IntArray::full(edge_parent, n@pre, l_edge_parent_next) *
										store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map_cur, heap_size) *
										has_permission(&minIndex)
						*/
						/*@ Given queue_map_cur */
						pqdk_update_or_push(heap_cost, heap_vertex, heap_pos, &heap_size, n, to_node, edge_weight)
							/*@ where M_before = queue_map_cur, n = heap_size, capacity = heap_capacity */;
						/*@ Assert
									exists current_edge selected l_first l_link l_from_new l_to_new l_weight_new
									       l_lowcost l_visited l_edge_parent
									       l_lowcost_cur l_lowcost_next l_edge_parent_next
								       queue_map_before queue_map_cur queue_map_next s s_after,
								2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
								2 * m@pre + 2 <= 100000 &&
								src == 0 &&
								n == n@pre && m == m@pre &&
								from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
									heap_capacity == 2 * m@pre + 2 &&
									0 <= heap_size && heap_size <= heap_capacity &&
									1 <= chosen && chosen <= n@pre &&
										0 <= selected && selected < n@pre &&
									0 <= cur_edge && cur_edge < 2 * m@pre &&
									0 <= to_node && to_node < n@pre &&
									INT_MIN <= edge_weight && edge_weight <= INT_MAX &&
									edge_weight < Znth(to_node, l_lowcost_cur, 0) &&
										Znth(to_node, replace_Znth(selected, 1, l_visited), 0) == 0 &&
									current_edge == Znth(cur_edge, l_link, 0) &&
									to_node == Znth(cur_edge, l_to_new, 0) &&
									edge_weight == Znth(cur_edge, l_weight_new, 0) &&
									queue_map_next == partial_map_update_or_add(queue_map_cur, to_node, edge_weight) &&
										prim_heap_scan_state(g, src, chosen, s, s_after,
										l_from_new, l_first, l_link, l_to_new, l_weight_new,
										l_lowcost, replace_Znth(selected, 1, l_visited), l_edge_parent,
										l_lowcost_next, l_edge_parent_next, current_edge, selected, min,
										queue_map_before, l_lowcost_next, l_edge_parent_next, queue_map_next, X) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
								array_graph(n@pre, m@pre, lf, lt, lw, g) &&
								PrimEnv(g, src) &&
								directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
								first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

								IntArray::full(from_arr@pre, m@pre, lf) *
								IntArray::full(to_arr@pre, m@pre, lt) *
								IntArray::full(weight_arr@pre, m@pre, lw) *
								IntArray::undef_full(out_u, n@pre - 1) *
								IntArray::undef_full(out_v, n@pre - 1) *
								IntArray::undef_full(out_wt, n@pre - 1) *
								IntArray::full(from_new, 2 * m@pre, l_from_new) *
								IntArray::full(to_new, 2 * m@pre, l_to_new) *
								IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
									IntArray::full(first, n@pre, l_first) *
									IntArray::full(link, 2 * m@pre, l_link) *
										IntArray::full(lowcost, n@pre, l_lowcost_next) *
										IntArray::full(visited, n@pre, replace_Znth(selected, 1, l_visited)) *
										IntArray::full(edge_parent, n@pre, l_edge_parent_next) *
										store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map_next, heap_size) *
										has_permission(&minIndex)
						*/
					}
					cur_edge = link[cur_edge];
				} else {
					cur_edge = -1;
				}
			}
			/*@ Assert
					exists selected l_first l_link l_from_new l_to_new l_weight_new
					       l_visited l_lowcost_next l_edge_parent_next queue_map s_after,
					2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
					2 * m@pre + 2 <= 100000 &&
					src == 0 &&
					n == n@pre && m == m@pre &&
					heap_capacity == 2 * m@pre + 2 &&
					1 <= chosen && chosen <= n@pre &&
					0 <= heap_size && heap_size <= heap_capacity &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
						prim_heap_loop_state(g, src, chosen, s_after,
							l_lowcost_next, replace_Znth(selected, 1, l_visited),
							l_edge_parent_next, queue_map, X) &&
					(chosen < n@pre => heap_size > 0) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
					(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
					PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

					IntArray::full(from_arr@pre, m@pre, lf) *
					IntArray::full(to_arr@pre, m@pre, lt) *
					IntArray::full(weight_arr@pre, m@pre, lw) *
					IntArray::undef_full(out_u, n@pre - 1) *
					IntArray::undef_full(out_v, n@pre - 1) *
					IntArray::undef_full(out_wt, n@pre - 1) *
					IntArray::full(from_new, 2 * m@pre, l_from_new) *
					IntArray::full(to_new, 2 * m@pre, l_to_new) *
					IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
						IntArray::full(first, n@pre, l_first) *
						IntArray::full(link, 2 * m@pre, l_link) *
						IntArray::full(lowcost, n@pre, l_lowcost_next) *
						IntArray::full(visited, n@pre, replace_Znth(selected, 1, l_visited)) *
							IntArray::full(edge_parent, n@pre, l_edge_parent_next) *
							store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size) *
							has_permission(&cur_edge) *
							has_permission(&minIndex) *
							has_permission(&min)
				*/
		}

		/*@ Assert
			exists l_first l_link l_from_new l_to_new l_weight_new
			       l_lowcost l_visited l_edge_parent queue_map s,
				2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
				n == n@pre && m == m@pre &&
				heap_capacity == 2 * m@pre + 2 &&
				chosen == n@pre &&
				0 <= heap_size && heap_size <= heap_capacity &&
				from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
				prim_heap_loop_state(g, src, chosen, s,
					l_lowcost, l_visited, l_edge_parent, queue_map, X) &&
				prim_heap_done_state(g, src, s, l_lowcost, l_visited, l_edge_parent, queue_map, X) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
				(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
				array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
				directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
				first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

				IntArray::full(from_arr@pre, m@pre, lf) *
				IntArray::full(to_arr@pre, m@pre, lt) *
				IntArray::full(weight_arr@pre, m@pre, lw) *
				IntArray::undef_full(out_u, n@pre - 1) *
				IntArray::undef_full(out_v, n@pre - 1) *
				IntArray::undef_full(out_wt, n@pre - 1) *
				IntArray::full(from_new, 2 * m@pre, l_from_new) *
				IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
				IntArray::full(link, 2 * m@pre, l_link) *
				IntArray::full(lowcost, n@pre, l_lowcost) *
				IntArray::full(visited, n@pre, l_visited) *
				IntArray::full(edge_parent, n@pre, l_edge_parent) *
				store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
		*/

			int out_i = 1;
		int mst_idx = 0;
		/*@ Inv Assert
			exists l_first l_link l_from_new l_to_new l_weight_new
		       l_lowcost l_visited l_edge_parent
		       l_out_u l_out_v l_out_wt queue_map s rg,
			2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
			2 * m@pre + 2 <= 100000 &&
			src == 0 &&
			n == n@pre && m == m@pre &&
			heap_capacity == 2 * m@pre + 2 &&
			chosen == n@pre &&
			from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
			1 <= out_i && out_i <= n@pre &&
			mst_idx <= n@pre - 1 &&
			mst_idx == out_i - 1 &&
			(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lf, 0) && Znth(a, lf, 0) < n@pre) &&
			(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lt, 0) && Znth(a, lt, 0) < n@pre) &&
			(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lw, 0) && Znth(a, lw, 0) < 1000000000) &&
			array_graph(n@pre, m@pre, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
			first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
			prim_heap_done_state(g, src, s, l_lowcost, l_visited, l_edge_parent, queue_map, X) &&
			growing_subgraph_state(g, s) &&
			visited_matches_state(g, s, l_visited) &&
			state_vertex_count(s) == n@pre &&
			selected_edges_match_state(g, src, s, l_edge_parent) &&
			lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
			prim_state_graph_matches(rg, s) &&
			prim_result_graph_matches_array_prefix(n@pre, mst_idx,
				l_out_u, l_out_v, l_out_wt, g, rg,
				l_edge_parent, l_from_new, l_to_new, l_weight_new) &&
			(forall (v: Z), 1 <= v && v < n@pre =>
				0 <= Znth(v, l_edge_parent, 0) && Znth(v, l_edge_parent, 0) < 2 * m@pre) &&
			(out_i < n@pre =>
				0 <= Znth(out_i, l_edge_parent, 0) && Znth(out_i, l_edge_parent, 0) < 2 * m@pre) &&
			safeExec(prim_state_is(s), return(tt), X) &&

			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			IntArray::seg(out_u, 0, mst_idx, l_out_u) *
			IntArray::undef_seg(out_u, mst_idx, n@pre - 1) *
			IntArray::seg(out_v, 0, mst_idx, l_out_v) *
			IntArray::undef_seg(out_v, mst_idx, n@pre - 1) *
			IntArray::seg(out_wt, 0, mst_idx, l_out_wt) *
			IntArray::undef_seg(out_wt, mst_idx, n@pre - 1) *
			IntArray::full(from_new, 2 * m@pre, l_from_new) *
			IntArray::full(to_new, 2 * m@pre, l_to_new) *
			IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
			IntArray::full(first, n@pre, l_first) *
			IntArray::full(link, 2 * m@pre, l_link) *
			IntArray::full(lowcost, n@pre, l_lowcost) *
			IntArray::full(visited, n@pre, l_visited) *
			IntArray::full(edge_parent, n@pre, l_edge_parent) *
			store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
		*/
		for (; out_i < n; out_i++) {
			/*@ Assert
				exists l_first l_link l_from_new l_to_new l_weight_new
			       l_lowcost l_visited l_edge_parent
			       l_out_u l_out_v l_out_wt queue_map s rg,
				2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
				2 * m@pre + 2 <= 100000 &&
				src == 0 &&
				n == n@pre && m == m@pre &&
				heap_capacity == 2 * m@pre + 2 &&
				chosen == n@pre &&
				from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
				1 <= out_i && out_i < n@pre &&
				mst_idx <= n@pre - 1 &&
				mst_idx == out_i - 1 &&
				(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lf, 0) && Znth(a, lf, 0) < n@pre) &&
				(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lt, 0) && Znth(a, lt, 0) < n@pre) &&
				(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lw, 0) && Znth(a, lw, 0) < 1000000000) &&
				array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
				directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
				first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
				prim_heap_done_state(g, src, s, l_lowcost, l_visited, l_edge_parent, queue_map, X) &&
				growing_subgraph_state(g, s) &&
				visited_matches_state(g, s, l_visited) &&
				state_vertex_count(s) == n@pre &&
				selected_edges_match_state(g, src, s, l_edge_parent) &&
				lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
				prim_state_graph_matches(rg, s) &&
				prim_result_graph_matches_array_prefix(n@pre, mst_idx,
					l_out_u, l_out_v, l_out_wt, g, rg,
					l_edge_parent, l_from_new, l_to_new, l_weight_new) &&
				(forall (v: Z), 1 <= v && v < n@pre =>
					0 <= Znth(v, l_edge_parent, 0) && Znth(v, l_edge_parent, 0) < 2 * m@pre) &&
				0 <= Znth(out_i, l_edge_parent, 0) && Znth(out_i, l_edge_parent, 0) < 2 * m@pre &&
				safeExec(prim_state_is(s), return(tt), X) &&

				IntArray::full(from_arr@pre, m@pre, lf) *
				IntArray::full(to_arr@pre, m@pre, lt) *
				IntArray::full(weight_arr@pre, m@pre, lw) *
				IntArray::seg(out_u, 0, mst_idx, l_out_u) *
				IntArray::undef_seg(out_u, mst_idx, n@pre - 1) *
				IntArray::seg(out_v, 0, mst_idx, l_out_v) *
				IntArray::undef_seg(out_v, mst_idx, n@pre - 1) *
				IntArray::seg(out_wt, 0, mst_idx, l_out_wt) *
				IntArray::undef_seg(out_wt, mst_idx, n@pre - 1) *
				IntArray::full(from_new, 2 * m@pre, l_from_new) *
				IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
				IntArray::full(link, 2 * m@pre, l_link) *
				IntArray::full(lowcost, n@pre, l_lowcost) *
				IntArray::full(visited, n@pre, l_visited) *
				IntArray::missing_i(edge_parent, out_i, 0, n@pre, l_edge_parent) *
				data_at(edge_parent + (out_i * sizeof(int)), int, Znth(out_i, l_edge_parent, 0)) *
				store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
			*/
			int edge_id = edge_parent[out_i];
			if (edge_id == -1) continue;
			if (0 <= edge_id && edge_id < 2 * m && mst_idx < n - 1) {
				/*@ Assert
					exists l_first l_link l_from_new l_to_new l_weight_new
				       l_lowcost l_visited l_edge_parent
				       l_out_u l_out_v l_out_wt queue_map s rg,
					0 <= edge_id && edge_id < 2 * m@pre &&
					mst_idx < n@pre - 1 &&
					edge_id == Znth(out_i, l_edge_parent, 0) &&
					2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre + 2 < INT_MAX && 4 * m@pre + 6 < INT_MAX &&
					2 * m@pre + 2 <= 100000 &&
					src == 0 &&
					n == n@pre && m == m@pre &&
					heap_capacity == 2 * m@pre + 2 &&
					chosen == n@pre &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
					1 <= out_i && out_i < n@pre &&
					mst_idx <= n@pre - 1 &&
					mst_idx == out_i - 1 &&
					(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lf, 0) && Znth(a, lf, 0) < n@pre) &&
					(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lt, 0) && Znth(a, lt, 0) < n@pre) &&
					(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lw, 0) && Znth(a, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
					PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
					prim_heap_done_state(g, src, s, l_lowcost, l_visited, l_edge_parent, queue_map, X) &&
					growing_subgraph_state(g, s) &&
					visited_matches_state(g, s, l_visited) &&
					state_vertex_count(s) == n@pre &&
					selected_edges_match_state(g, src, s, l_edge_parent) &&
					lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
					prim_state_graph_matches(rg, s) &&
					prim_result_graph_matches_array_prefix(n@pre, mst_idx,
						l_out_u, l_out_v, l_out_wt, g, rg,
						l_edge_parent, l_from_new, l_to_new, l_weight_new) &&
					(forall (v: Z), 1 <= v && v < n@pre =>
						0 <= Znth(v, l_edge_parent, 0) && Znth(v, l_edge_parent, 0) < 2 * m@pre) &&
					safeExec(prim_state_is(s), return(tt), X) &&

					IntArray::full(from_arr@pre, m@pre, lf) *
					IntArray::full(to_arr@pre, m@pre, lt) *
					IntArray::full(weight_arr@pre, m@pre, lw) *
					IntArray::seg(out_u, 0, mst_idx, l_out_u) *
					IntArray::undef_seg(out_u, mst_idx, n@pre - 1) *
					IntArray::seg(out_v, 0, mst_idx, l_out_v) *
					IntArray::undef_seg(out_v, mst_idx, n@pre - 1) *
					IntArray::seg(out_wt, 0, mst_idx, l_out_wt) *
					IntArray::undef_seg(out_wt, mst_idx, n@pre - 1) *
					IntArray::missing_i(from_new, edge_id, 0, 2 * m@pre, l_from_new) *
					data_at(from_new + (edge_id * sizeof(int)), int, Znth(edge_id, l_from_new, 0)) *
					IntArray::missing_i(to_new, edge_id, 0, 2 * m@pre, l_to_new) *
					data_at(to_new + (edge_id * sizeof(int)), int, Znth(edge_id, l_to_new, 0)) *
					IntArray::missing_i(weight_new, edge_id, 0, 2 * m@pre, l_weight_new) *
					data_at(weight_new + (edge_id * sizeof(int)), int, Znth(edge_id, l_weight_new, 0)) *
					IntArray::full(first, n@pre, l_first) *
					IntArray::full(link, 2 * m@pre, l_link) *
					IntArray::full(lowcost, n@pre, l_lowcost) *
					IntArray::full(visited, n@pre, l_visited) *
					IntArray::missing_i(edge_parent, out_i, 0, n@pre, l_edge_parent) *
					data_at(edge_parent + (out_i * sizeof(int)), int, Znth(out_i, l_edge_parent, 0)) *
					store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
				*/
				out_u[mst_idx] = from_new[edge_id];
				out_v[mst_idx] = to_new[edge_id];
				out_wt[mst_idx] = weight_new[edge_id];
				mst_idx++;
			}
		}

	/*@ Assert
		exists lru lrv lrwt rg
		       l_from_new l_to_new l_weight_new l_first l_link
		       l_lowcost l_visited l_edge_parent queue_map s,
			safeExec(prim_state_graph_matches(rg), return(tt), X) &&
			prim_result_graph_matches_array(n@pre, lru, lrv, lrwt, g, rg) &&
			chosen == n@pre &&
			heap_capacity == 2 * m@pre + 2 &&
			0 <= heap_capacity &&
			prim_heap_done_state(g, src, s, l_lowcost, l_visited, l_edge_parent, queue_map, X) &&

			IntArray::full(out_u, n@pre - 1, lru) *
			IntArray::full(out_v, n@pre - 1, lrv) *
			IntArray::full(out_wt, n@pre - 1, lrwt) *
			IntArray::full(from_arr@pre, m@pre, lf) *
			IntArray::full(to_arr@pre, m@pre, lt) *
			IntArray::full(weight_arr@pre, m@pre, lw) *
			has_permission(&n) *
			has_permission(&m) *
			has_permission(&from_arr) *
			has_permission(&to_arr) *
			has_permission(&weight_arr) *
			has_permission(&out_i) *
			has_permission(&mst_idx) *
			IntArray::full(from_new, 2 * m@pre, l_from_new) *
			IntArray::full(to_new, 2 * m@pre, l_to_new) *
			IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
			IntArray::full(first, n@pre, l_first) *
			IntArray::full(link, 2 * m@pre, l_link) *
			IntArray::full(lowcost, n@pre, l_lowcost) *
			IntArray::full(visited, n@pre, l_visited) *
			IntArray::full(edge_parent, n@pre, l_edge_parent) *
			store_heap(heap_cost, heap_vertex, heap_pos, n@pre, heap_capacity, queue_map, heap_size)
		*/

		struct mst_tree* p = malloc_mst_tree();
	p->u = out_u;
	p->v = out_v;
	p->wt = out_wt;
	return p;
}
