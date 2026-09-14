#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "safeexec_def.h"

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Prim.prim_forward_star_lib */
/*@ Import Coq Require Import ListLib.Base.Positional */
/*@ Extern Coq (St :: *) */
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
/*@ Extern Coq (prim_result_graph_matches_array: Z -> list Z -> list Z -> list Z -> G -> G -> Prop) */
/*@ Extern Coq (prim_result_graph_matches_array_prefix: Z -> Z -> list Z -> list Z -> list Z -> G -> G -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (first_link_matches_inserted_vertex_directed_edges: G -> Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (first_link_matches_vertex_directed_edges: G -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (growing_subgraph_state: G -> St -> Prop) */
/*@ Extern Coq (visited_matches_state: G -> St -> list Z -> Prop) */
/*@ Extern Coq (state_vertex_count: St -> Z) */
/*@ Extern Coq (parent_edges_match_state: G -> V -> St -> list Z -> Prop) */
/*@ Extern Coq (lowcost_parent_match: G -> St -> list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (candidate_vertex_exists_in_range: Z -> G -> St -> list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (min_vertex_in_range: G -> St -> Z -> Z -> V -> list Z -> list Z -> Prop) */
/*@ Extern Coq (selected_parent_edge_is_min_cut_edge: G -> St -> list Z -> V -> Prop) */
/*@ Extern Coq (selected_parent_pair: G -> St -> list Z -> list Z -> list Z -> V -> V -> V -> Prop) */
/*@ Extern Coq (selected_parent_add_to_mst: G -> St -> St -> list Z -> list Z -> list Z -> V -> Prop) */
/*@ Extern Coq (selected_state_after_add: G -> V -> Z -> Z -> St -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_prefix_update: G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> Z -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (scan_one_directed_edge_update: G -> St -> list Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_update: G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> list Z -> list Z -> list Z -> list Z -> Prop) */

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

struct mst_tree* prim(int* from_arr, int* to_arr, int* weight_arr, int n, int m)
/*@ high_level_spec <= low_level_spec
	With (lf: list Z) (lt: list Z) (lw: list Z) (g : G) (src: V) X
		Require
			src == 0 &&
			2 <= n && n < INT_MAX &&
			1 <= m && 2 * m < INT_MAX &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n) &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n) &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n, m, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr, m, lf) *
			IntArray::full(to_arr, m, lt) *
			IntArray::full(weight_arr, m, lw)
	Ensure
		exists lru lrv lrwt rg
			   r_from_new r_to_new r_weight_new r_first r_link r_lowcost r_visited r_edge_parent
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
			IntArray::full(r_edge_parent, n, l_edge_parent_ret)
*/
;

struct mst_tree* prim(int* from_arr, int* to_arr, int* weight_arr, int n, int m)
/*@ low_level_spec
	With (lf: list Z) (lt: list Z) (lw: list Z) (g : G) (src: V) X
		Require
				src == 0 &&
			2 <= n && n < INT_MAX &&
			1 <= m && 2 * m < INT_MAX &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n) &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n) &&
				(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&

				safeExec(initStPred(g, src), Prim2(g), X) &&
			array_graph(n, m, lf, lt, lw, g) &&
			PrimEnv(g, src) &&

			IntArray::full(from_arr, m, lf) *
		IntArray::full(to_arr, m, lt) *
		IntArray::full(weight_arr, m, lw) 
	Ensure
			exists lru lrv lrwt rg
				   r_from_new r_to_new r_weight_new r_first r_link r_lowcost r_visited r_edge_parent
				   l_from_new_ret l_to_new_ret l_weight_new_ret l_first_ret l_link_ret
				   l_lowcost_ret l_visited_ret l_edge_parent_ret,
			safeExec(prim_state_graph_matches(rg), return(tt), X) &&
			__return != 0 &&
				prim_result_graph_matches_array(n, lru, lrv, lrwt, g, rg) &&

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
			IntArray::full(r_edge_parent, n, l_edge_parent_ret)
*/
{
	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_wt = malloc_int_array(n - 1);

    int* from_new = malloc_int_array(2*m);
    int* to_new = malloc_int_array(2*m);
    int* weight_new = malloc_int_array(2*m);
		int i = 0;
		
		/*@ Inv Assert
			exists l_from_new_prefix
			       l_to_new_prefix
			       l_weight_new_prefix,
				2 <= n@pre && n@pre < INT_MAX &&
				1 <= m@pre && 2 * m@pre < INT_MAX &&
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
        from_new[2*i] = from_arr[i];
        to_new[2*i] = to_arr[i];
        weight_new[2*i] = weight_arr[i];

        from_new[2*i + 1] = to_arr[i];
        to_new[2*i + 1] = from_arr[i];
        weight_new[2*i + 1] = weight_arr[i];
    }
	
		int* first = malloc_int_array(n);
		int* link = malloc_int_array(2 * m);
		 i = 0;
	/*@ Inv Assert
		exists l_from_new l_to_new l_weight_new,
			2 <= n@pre && n@pre < INT_MAX &&
			1 <= m@pre && 2 * m@pre < INT_MAX &&
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
			IntArray::full(from_new, 2 * m@pre, l_from_new) *
			IntArray::full(to_new, 2 * m@pre, l_to_new) *
			IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
			IntArray::seg(first, 0, i, repeat_Z(-1, i)) *
			IntArray::undef_seg(first, i, n@pre) *
			IntArray::undef_full(link, 2 * m@pre)
	*/
	for (; i < n; i++) {
		first[i] = -1;
	}

	i = 0;
	/*@ Inv Assert
		exists l_from_new l_to_new l_weight_new,
			2 <= n@pre && n@pre < INT_MAX &&
			1 <= m@pre && 2 * m@pre < INT_MAX &&
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
		

		i = 0;
		/*@ Inv Assert
		exists l_first l_link l_from_new l_to_new l_weight_new,
			2 <= n@pre && n@pre < INT_MAX &&
			1 <= m@pre && 2 * m@pre < INT_MAX &&
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
				1 <= m@pre && 2 * m@pre < INT_MAX &&
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
				IntArray::full(from_new, 2 * m@pre, l_from_new) *
				IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
				IntArray::full(link, 2 * m@pre, l_link)
		*/
			int tmp = first[u];
			first[u] = i;
			link[i] = tmp;
		}
		
	int* visited = malloc_int_array(n);
		int* lowcost = malloc_int_array(n);
		int* edge_parent = malloc_int_array(n);
		i = 0;
		
				/*@ Inv Assert
					exists l_first l_link l_from_new l_to_new l_weight_new,
					2 <= n@pre && n@pre < INT_MAX &&
					1 <= m@pre && 2 * m@pre < INT_MAX &&
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
				lowcost[i] = 1000000000;
				visited[i] = 0;
			edge_parent[i] = -1;
		}
		/*@ Assert
			exists l_first l_link l_from_new l_to_new l_weight_new,
			2 <= n@pre && n@pre < INT_MAX &&
			1 <= m@pre && 2 * m@pre < INT_MAX &&
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

		lowcost[0] = 0;
		i = 0;
		
				/*@ Inv
					boot:
						exists l_first l_link l_from_new l_to_new l_weight_new,
						2 <= n@pre && n@pre < INT_MAX &&
						1 <= m@pre && 2 * m@pre < INT_MAX &&
						src == 0 &&
						n == n@pre && m == m@pre &&
						from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
						i == 0 &&
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
						IntArray::full(edge_parent, n@pre, repeat_Z(-1, n@pre));
					running:
						exists l_first l_link l_from_new l_to_new l_weight_new
							   l_lowcost l_visited l_edge_parent s,
						2 <= n@pre && n@pre < INT_MAX &&
						1 <= m@pre && 2 * m@pre < INT_MAX &&
						src == 0 &&
						n == n@pre && m == m@pre &&
						from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
						1 <= i && i <= n@pre &&
						(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
						(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
						(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
						array_graph(n@pre, m@pre, lf, lt, lw, g) &&
						PrimEnv(g, src) &&
						directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
						first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

						growing_subgraph_state(g, s) &&
						visited_matches_state(g, s, l_visited) &&
						state_vertex_count(s) == i &&
						parent_edges_match_state(g, src, s, l_edge_parent) &&
						lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
						(i < n@pre => candidate_vertex_exists_in_range(n@pre, g, s, l_lowcost, l_edge_parent, 1000000000)) &&

						safeExec(prim_state_is(s), Prim2_loop(g, i - 1), X) &&

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
						IntArray::full(edge_parent, n@pre, l_edge_parent)
					with
					all ==> boot
					boot ==> running
					running ==> running
				*/
					for (; i < n; i++) {
						int min = 1000000000;
						int minIndex = -1;
					int j =0;
						/*@ Inv Assert
							exists l_first l_link l_from_new l_to_new l_weight_new
								   l_lowcost l_visited l_edge_parent s,
							2 <= n@pre && n@pre < INT_MAX &&
							1 <= m@pre && 2 * m@pre < INT_MAX &&
							src == 0 &&
							n == n@pre && m == m@pre &&
							from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
							0 <= j && j <= n@pre &&
							(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
							(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
							(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
							array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
							directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
							first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

							((i == 0 &&
							  safeExec(initStPred(g, src), Prim2(g), X) &&
							  (j == 0 => min == 1000000000 && minIndex == -1) &&
							  (1 <= j => min == 0 && minIndex == 0) &&
							  (minIndex != -1 => 0 <= minIndex && minIndex < j) &&
							  l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
							  l_visited == repeat_Z(0, n@pre) &&
							  l_edge_parent == repeat_Z(-1, n@pre))
							 ||
								 (1 <= i && i < n@pre &&
									  safeExec(prim_state_is(s), Prim2_loop(g, i - 1), X) &&
									  growing_subgraph_state(g, s) &&
									  visited_matches_state(g, s, l_visited) &&
									  state_vertex_count(s) == i &&
									  parent_edges_match_state(g, src, s, l_edge_parent) &&
									  lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
								  (i < n@pre => candidate_vertex_exists_in_range(n@pre, g, s, l_lowcost, l_edge_parent, 1000000000)) &&
								  min_vertex_in_range(g, s, j, 1000000000, minIndex, l_lowcost, l_edge_parent) &&
							  (minIndex == -1 => min == 1000000000) &&
								  (minIndex != -1 => min == Znth(minIndex, l_lowcost, 0)) &&
							  (minIndex != -1 => 0 <= minIndex && minIndex < j))) &&

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
							IntArray::full(edge_parent, n@pre, l_edge_parent)
						*/
					for (; j < n; j++) {
					if (visited[j] == 0) {
						if (lowcost[j] < min) {
							min = lowcost[j];
							minIndex = j;
						}
					}
				    }
							/*@ Assert
								exists l_first l_link l_from_new l_to_new l_weight_new
									   l_lowcost l_visited l_edge_parent s,
								2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre < INT_MAX &&
								src == 0 &&
								n == n@pre && m == m@pre &&
								from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
										j == n@pre &&
										0 <= minIndex && minIndex < n@pre &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
								array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
								directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
								first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

								((i == 0 &&
								  safeExec(initStPred(g, src), Prim2(g), X) &&
								  min == 0 &&
								  minIndex == 0 &&
								  l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
								  l_visited == repeat_Z(0, n@pre) &&
								  l_edge_parent == repeat_Z(-1, n@pre)) 
								||
										 (1 <= i && i < n@pre &&
										  safeExec(prim_state_is(s), Prim2_loop(g, i - 1), X) &&
										  growing_subgraph_state(g, s) &&
											  visited_matches_state(g, s, l_visited) &&
											  state_vertex_count(s) == i &&
											  parent_edges_match_state(g, src, s, l_edge_parent) &&
											  lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
									  candidate_vertex_exists_in_range(n@pre, g, s, l_lowcost, l_edge_parent, 1000000000) &&
									  minIndex != -1 &&
									  min == Znth(minIndex, l_lowcost, 0) &&
									  selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent, minIndex) &&
									  min_vertex_in_range(g, s, n@pre, 1000000000, minIndex, l_lowcost, l_edge_parent))) &&
								  
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
								IntArray::full(edge_parent, n@pre, l_edge_parent)
						*/
						
					if (minIndex != -1) {
						visited[minIndex] = 1;
							/*@ Assert
								exists l_first l_link l_from_new l_to_new l_weight_new
									   l_lowcost l_visited l_edge_parent s,
								2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre < INT_MAX &&
								src == 0 &&
								n == n@pre && m == m@pre &&
								from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
									j == n@pre &&
									minIndex != -1 &&
									0 <= minIndex && minIndex < n@pre &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n@pre) &&
								(forall (k: Z), (0 <= k && k < m@pre) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
								array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
								directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
								first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

								((i == 0 &&
								  safeExec(initStPred(g, src), Prim2(g), X) &&
								  min == 0 &&
								  minIndex == 0 &&
								  l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
								  l_visited == repeat_Z(0, n@pre) &&
								  l_edge_parent == repeat_Z(-1, n@pre)) 
								  ||
									 (exists x_u x_v s_next,
									  1 <= i && i < n@pre &&
									  safeExec(prim_state_is(s_next), Prim2_loop(g, i), X) &&
									  growing_subgraph_state(g, s) &&
									  visited_matches_state(g, s, l_visited) &&
									  state_vertex_count(s) == i &&
									  parent_edges_match_state(g, src, s, l_edge_parent) &&
									  lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
											  min == Znth(minIndex, l_lowcost, 0) &&
										  selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent, minIndex) &&
											  selected_parent_pair(g, s, l_from_new, l_to_new, l_edge_parent, minIndex, x_u, x_v) &&
											  selected_parent_add_to_mst(g, s, s_next, l_from_new, l_to_new, l_edge_parent, minIndex) &&
												  visited_matches_state(g, s_next, replace_Znth(minIndex, 1, l_visited)) &&
												  state_vertex_count(s_next) == i + 1 &&
												  parent_edges_match_state(g, src, s_next, l_edge_parent) &&
												  min_vertex_in_range(g, s, n@pre, 1000000000, minIndex, l_lowcost, l_edge_parent))) &&

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
									IntArray::full(visited, n@pre, replace_Znth(minIndex, 1, l_visited)) *
									IntArray::full(edge_parent, n@pre, l_edge_parent)	
							*/
								
							
							int cur_edge = first[minIndex];
						/*@ Inv Assert
							exists (current_e : Z) (l_first : list Z) (l_link : list Z)
								   (l_from_new : list Z) (l_to_new : list Z) (l_weight_new : list Z)
								   (l_lowcost : list Z) (l_visited : list Z) (l_edge_parent : list Z)
								   (l_lowcost_cur : list Z) (l_edge_parent_cur : list Z)
								   (s : St) (s_after : St),
							2 <= n@pre && n@pre < INT_MAX &&
							1 <= m@pre && 2 * m@pre < INT_MAX &&
							src == 0 &&
							n == n@pre && m == m@pre &&
							from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
							j == n@pre &&
							minIndex != -1 &&
							0 <= minIndex && minIndex < n@pre &&
							cur_edge == current_e &&
							(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lf, 0) && Znth(a, lf, 0) < n@pre) &&
							(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lt, 0) && Znth(a, lt, 0) < n@pre) &&
							(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lw, 0) && Znth(a, lw, 0) < 1000000000) &&
							array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
							directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
							first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

							((i == 0 &&
							  min == 0 &&
							  minIndex == 0 &&
							  l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
							  l_visited == repeat_Z(0, n@pre) &&
							  l_edge_parent == repeat_Z(-1, n@pre))
							||
								 (exists x_u x_v s_next,
								  1 <= i && i < n@pre &&
								  growing_subgraph_state(g, s) &&
									  visited_matches_state(g, s, l_visited) &&
									  state_vertex_count(s) == i &&
									  parent_edges_match_state(g, src, s, l_edge_parent) &&
									  lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&

							  min == Znth(minIndex, l_lowcost, 0) &&
							  selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent, minIndex) &&
								  selected_parent_pair(g, s, l_from_new, l_to_new, l_edge_parent, minIndex, x_u, x_v) &&
								  selected_parent_add_to_mst(g, s, s_next, l_from_new, l_to_new, l_edge_parent, minIndex) &&
									  visited_matches_state(g, s_next, replace_Znth(minIndex, 1, l_visited)) &&
									  state_vertex_count(s_next) == i + 1 &&
									  parent_edges_match_state(g, src, s_next, l_edge_parent) &&
									  min_vertex_in_range(g, s, n@pre, 1000000000, minIndex, l_lowcost, l_edge_parent))) &&
								selected_state_after_add(g, src, i, n@pre, s, s_after,
									l_from_new, l_to_new, l_edge_parent, l_lowcost, l_visited, minIndex) &&

									safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&
									state_vertex_count(s_after) == i + 1 &&
									parent_edges_match_state(g, src, s_after, l_edge_parent_cur) &&
									scan_minIndex_adjacency_prefix_update(g, s_after,
								l_from_new, l_first, l_link, l_to_new, l_weight_new,
								minIndex, current_e, l_lowcost, l_edge_parent,
								l_lowcost_cur, l_edge_parent_cur) &&

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
								IntArray::full(lowcost, n, l_lowcost_cur) *
									IntArray::full(visited, n, replace_Znth(minIndex, 1, l_visited)) *
									IntArray::full(edge_parent, n, l_edge_parent_cur)
							*/

						while (cur_edge != -1) {
								if (0 <= cur_edge && cur_edge < 2 * m) {
										int to_node = to_new[cur_edge];
										int edge_weight = weight_new[cur_edge];
									
													if (0 <= to_node && to_node < n && visited[to_node] == 0 && edge_weight < lowcost[to_node]) 
											 {
									lowcost[to_node] = edge_weight;
									edge_parent[to_node] = cur_edge;
												}
									
								cur_edge = link[cur_edge];
							/*@ Assert
								exists current_e l_first l_link l_from_new l_to_new l_weight_new
									   l_lowcost l_visited l_edge_parent
									   l_lowcost_next l_edge_parent_next s s_after,
								2 <= n@pre && n@pre < INT_MAX &&
								1 <= m@pre && 2 * m@pre < INT_MAX &&
								src == 0 &&
								n == n@pre && m == m@pre &&
								from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
								j == n@pre &&
								minIndex != -1 &&
								0 <= minIndex && minIndex < n@pre &&
								cur_edge == Znth(current_e, l_link, 0) &&
								0 <= current_e && current_e < 2 * m@pre &&
								(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lf, 0) && Znth(a, lf, 0) < n@pre) &&
								(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lt, 0) && Znth(a, lt, 0) < n@pre) &&
								(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lw, 0) && Znth(a, lw, 0) < 1000000000) &&
								array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
								directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
								first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

								safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&

								((i == 0 &&
								  min == 0 &&
								  minIndex == 0 &&
								  l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
								  l_visited == repeat_Z(0, n@pre) &&
								  l_edge_parent == repeat_Z(-1, n@pre)) ||
								 (exists x_u x_v s_next,
								  1 <= i && i < n@pre &&
								  growing_subgraph_state(g, s) &&
									  visited_matches_state(g, s, l_visited) &&
									  state_vertex_count(s) == i &&
									  parent_edges_match_state(g, src, s, l_edge_parent) &&
									  lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
								  min == Znth(minIndex, l_lowcost, 0) &&
								  selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent, minIndex) &&
								  selected_parent_pair(g, s, l_from_new, l_to_new, l_edge_parent, minIndex, x_u, x_v) &&
								  selected_parent_add_to_mst(g, s, s_next, l_from_new, l_to_new, l_edge_parent, minIndex) &&
									  visited_matches_state(g, s_next, replace_Znth(minIndex, 1, l_visited)) &&
									  state_vertex_count(s_next) == i + 1 &&
									  parent_edges_match_state(g, src, s_next, l_edge_parent) &&
									  min_vertex_in_range(g, s, n@pre, 1000000000, minIndex, l_lowcost, l_edge_parent))) &&
										selected_state_after_add(g, src, i, n@pre, s, s_after,
										l_from_new, l_to_new, l_edge_parent, l_lowcost, l_visited, minIndex) &&
										state_vertex_count(s_after) == i + 1 &&
										parent_edges_match_state(g, src, s_after, l_edge_parent_next) &&
											scan_minIndex_adjacency_prefix_update(g, s_after,
										l_from_new, l_first, l_link, l_to_new, l_weight_new,
										minIndex, cur_edge, l_lowcost, l_edge_parent,
										l_lowcost_next, l_edge_parent_next) &&

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
									IntArray::full(visited, n@pre, replace_Znth(minIndex, 1, l_visited)) *
									IntArray::full(edge_parent, n@pre, l_edge_parent_next) *
									has_permission(&to_node) *
									has_permission(&edge_weight)
							*/
					} else {
						cur_edge = -1;
					}
				}
				/*@ Assert
					exists l_first l_link l_from_new l_to_new l_weight_new
						   l_lowcost l_visited l_edge_parent
						   l_lowcost_next l_edge_parent_next s s_after,
					2 <= n@pre && n@pre < INT_MAX &&
					1 <= m@pre && 2 * m@pre < INT_MAX &&
					src == 0 &&
					n == n@pre && m == m@pre &&
					from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
					0 <= i && i < n@pre &&
					j == n@pre &&
					minIndex != -1 &&
					0 <= minIndex && minIndex < n@pre &&
					cur_edge == -1 &&
					(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lf, 0) && Znth(a, lf, 0) < n@pre) &&
					(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lt, 0) && Znth(a, lt, 0) < n@pre) &&
					(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lw, 0) && Znth(a, lw, 0) < 1000000000) &&
					array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
					directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
					first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&

					safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&

					((i == 0 &&
					  min == 0 &&
					  minIndex == 0 &&
					  l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
					  l_visited == repeat_Z(0, n@pre) &&
					  l_edge_parent == repeat_Z(-1, n@pre)) ||
						 (exists x_u x_v s_next,
						  1 <= i && i < n@pre &&
						  growing_subgraph_state(g, s) &&
							  visited_matches_state(g, s, l_visited) &&
								  state_vertex_count(s) == i &&
							  parent_edges_match_state(g, src, s, l_edge_parent) &&
							  lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
					  min == Znth(minIndex, l_lowcost, 0) &&
					  selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent, minIndex) &&
						  selected_parent_pair(g, s, l_from_new, l_to_new, l_edge_parent, minIndex, x_u, x_v) &&
						  selected_parent_add_to_mst(g, s, s_next, l_from_new, l_to_new, l_edge_parent, minIndex) &&
							  visited_matches_state(g, s_next, replace_Znth(minIndex, 1, l_visited)) &&
								  state_vertex_count(s_next) == i + 1 &&
							  parent_edges_match_state(g, src, s_next, l_edge_parent) &&
							  min_vertex_in_range(g, s, n@pre, 1000000000, minIndex, l_lowcost, l_edge_parent))) &&
							selected_state_after_add(g, src, i, n@pre, s, s_after,
							l_from_new, l_to_new, l_edge_parent, l_lowcost, l_visited, minIndex) &&
							state_vertex_count(s_after) == i + 1 &&
							parent_edges_match_state(g, src, s_after, l_edge_parent_next) &&
							scan_minIndex_adjacency_prefix_update(g, s_after,
						l_from_new, l_first, l_link, l_to_new, l_weight_new,
						minIndex, cur_edge, l_lowcost, l_edge_parent,
						l_lowcost_next, l_edge_parent_next) &&
						growing_subgraph_state(g, s_after) &&
						visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
						parent_edges_match_state(g, src, s_after, l_edge_parent_next) &&
						lowcost_parent_match(g, s_after, l_lowcost_next, l_edge_parent_next, 1000000000) &&

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
					IntArray::full(visited, n@pre, replace_Znth(minIndex, 1, l_visited)) *
					IntArray::full(edge_parent, n@pre, l_edge_parent_next)
				*/
				/*@ boot ==> running */
				
			}
	}




	i = 1;
	int mst_idx = 0;
	/*@ Inv Assert
		exists l_first l_link l_from_new l_to_new l_weight_new
			   l_lowcost l_visited l_edge_parent
			   l_out_u l_out_v l_out_wt s rg,
		2 <= n@pre && n@pre < INT_MAX &&
		1 <= m@pre && 2 * m@pre < INT_MAX &&
		src == 0 &&
		n == n@pre && m == m@pre &&
		from_arr == from_arr@pre && to_arr == to_arr@pre && weight_arr == weight_arr@pre &&
		1 <= i && i <= n@pre &&
			mst_idx <= n@pre - 1 &&
			mst_idx == i - 1 &&
		(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lf, 0) && Znth(a, lf, 0) < n@pre) &&
		(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lt, 0) && Znth(a, lt, 0) < n@pre) &&
		(forall (a: Z), (0 <= a && a < m@pre) => 0 <= Znth(a, lw, 0) && Znth(a, lw, 0) < 1000000000) &&
		array_graph(n@pre, m@pre, lf, lt, lw, g) &&
				PrimEnv(g, src) &&
		directed_array_graph(g, l_from_new, l_to_new, l_weight_new) &&
			first_link_matches_vertex_directed_edges(g, l_from_new, l_first, l_link) &&
			
				growing_subgraph_state(g, s) &&
				visited_matches_state(g, s, l_visited) &&
				state_vertex_count(s) == n@pre &&
				parent_edges_match_state(g, src, s, l_edge_parent) &&
					lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
					prim_state_graph_matches(rg, s) &&
							prim_result_graph_matches_array_prefix(n@pre, mst_idx,
								l_out_u, l_out_v, l_out_wt, g, rg,
								l_edge_parent, l_from_new, l_to_new, l_weight_new) &&
				(forall (v: Z), 1 <= v && v < n@pre =>
					0 <= Znth(v, l_edge_parent, 0) && Znth(v, l_edge_parent, 0) < 2 * m@pre) &&
			(i < n@pre =>
				0 <= Znth(i, l_edge_parent, 0) && Znth(i, l_edge_parent, 0) < 2 * m@pre) &&

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
		IntArray::full(edge_parent, n@pre, l_edge_parent)
	*/
	for (; i < n; i++) {
		if (edge_parent[i] == -1) continue;
		int edge_id = edge_parent[i];
		if (0 <= edge_id && edge_id < 2 * m && mst_idx < n - 1) {
			out_u[mst_idx] = from_new[edge_id];
			out_v[mst_idx] = to_new[edge_id];
			out_wt[mst_idx] = weight_new[edge_id];
			mst_idx++;
		}
	}

	/*@ Assert
		exists lru lrv lrwt rg
			   l_from_new l_to_new l_weight_new l_first l_link
			   l_lowcost l_visited l_edge_parent,
			safeExec(prim_state_graph_matches(rg), return(tt), X) &&
			prim_result_graph_matches_array(n@pre, lru, lrv, lrwt, g, rg) &&

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
					has_permission(&i) *
					has_permission(&mst_idx) *
					IntArray::full(from_new, 2 * m@pre, l_from_new) *
				IntArray::full(to_new, 2 * m@pre, l_to_new) *
				IntArray::full(weight_new, 2 * m@pre, l_weight_new) *
				IntArray::full(first, n@pre, l_first) *
				IntArray::full(link, 2 * m@pre, l_link) *
				IntArray::full(lowcost, n@pre, l_lowcost) *
				IntArray::full(visited, n@pre, l_visited) *
				IntArray::full(edge_parent, n@pre, l_edge_parent)
	*/

	struct mst_tree* p = malloc_mst_tree();
	p->u = out_u;
	p->v = out_v;
	p->wt = out_wt;
	return p;	
}
