#include "safeexec_def.h"
#include "../../Data_structures/union_find/union_find_def.h"
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (G :: *) */
/*@ Extern Coq (KruskalEnv : G -> Prop) */
/*@ Extern Coq (Zrange : Z -> Z -> list Z) */
/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (array_graph : Z -> Z -> list Z -> list Z -> list Z -> G -> Prop) */
/*@ Extern Coq (edge_arrays_ordered_by : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (after_sorted_edge_of_input : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (same_outside_edge_arrays_range : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (edge_arrays_partitioned_by_weight_at : list Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (edge_arrays_range_sorted_by_weight : list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (St :: *) */
/*@ Extern Coq (kruskal_scan_state : G -> list Z -> Z -> Z -> St -> Prop) */
/*@ Extern Coq (kruskal_scan_phase : G -> St -> Z -> Prop) */
/*@ Extern Coq (output_prefix_matches_state : G -> Z -> list Z -> list Z -> list Z -> St -> Prop) */
/*@ Extern Coq (initStPred : G -> St -> Prop) */
/*@ Extern Coq (KruskalProg : G -> program St unit) */
/*@ Extern Coq (kruskal_state_is : St -> St -> Prop) */
/*@ Extern Coq (kruskal_state_graph_matches : G -> St -> Prop) */
/*@ Extern Coq (union_find_connectivity_matches_state : G -> St -> (Z -> Z) -> Prop) */
/*@ Extern Coq (selected_edge_is_min_edge : G -> list Z -> Z -> St -> Z -> Prop) */
/*@ Extern Coq (selected_edge_pair : G -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (selected_edge_add_to_mst : St -> St -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (return_is_mst : G -> G -> Prop) */
/*@ Extern Coq (kruskal_result_graph_matches_array : list Z -> list Z -> list Z -> G -> G -> Prop) */
/*@ Import Coq Local Open Scope monad */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Kruskal.kruskal_union_find_lib */
/*@ Import Coq Require Import ListLib.Base.Positional */
/*@ Import Coq From SumLib Require Import ZRange */

int* malloc_int_array(int n)
/*@ Require n > 0 && emp
	Ensure IntArray::undef_full(__return, n)
*/
;

void free_int_array(int* a)
/*@ With n l
	Require IntArray::full(a, n, l)
	Ensure emp
*/
;

struct mst_tree {
	int* ru;
	int* rv;
	int* rw;
};

struct mst_tree* malloc_mst_tree()
/*@ Require emp
	Ensure __return != 0 &&
		has_permission(&(__return -> ru)) *
		has_permission(&(__return -> rv)) *
		has_permission(&(__return -> rw))
*/
;

void swap_int(int* a, int* b)
/*@ neq
	With x y
	Require x == *a && y == *b
	Ensure y == *a && x == *b
*/
{
	int t = *a;
	*a = *b;
	*b = t;
}

void swap_edge(int* u, int* v, int* w, int i, int j)
/*@ With n l_u l_v l_w
	Require 0 <= i && i < n && 0 <= j && j < n &&
			Zlength(l_u) == n && Zlength(l_v) == n && Zlength(l_w) == n &&
			IntArray::full(u, n, l_u) *
			IntArray::full(v, n, l_v) *
			IntArray::full(w, n, l_w)
	Ensure u == u@pre && v == v@pre && w == w@pre &&
			i == i@pre && j == j@pre &&
			Zlength(l_u) == n && Zlength(l_v) == n && Zlength(l_w) == n &&
			IntArray::full(u, n,
				replace_Znth(j, l_u[i], replace_Znth(i, l_u[j], l_u))) *
			IntArray::full(v, n,
				replace_Znth(j, l_v[i], replace_Znth(i, l_v[j], l_v))) *
			IntArray::full(w, n,
				replace_Znth(j, l_w[i], replace_Znth(i, l_w[j], l_w)))
*/
{
	if (i != j) {
		if (i < j) {
			/*@ Assert
				 u == u@pre && v == v@pre && w == w@pre &&
				i == i@pre && j == j@pre &&
				0 <= i && i < j && j < n &&
				Zlength(l_u) == n && Zlength(l_v) == n && Zlength(l_w) == n &&
				IntArray::seg(u, 0, j, sublist(0, j, l_u)) *
				IntArray::seg(u, j, n, sublist(j, n, l_u)) *
				IntArray::seg(v, 0, j, sublist(0, j, l_v)) *
				IntArray::seg(v, j, n, sublist(j, n, l_v)) *
				IntArray::seg(w, 0, j, sublist(0, j, l_w)) *
				IntArray::seg(w, j, n, sublist(j, n, l_w))
			*/
			swap_int(&u[i], &u[j]) /*@ where (neq) x = l_u[i], y = l_u[j] */;
			swap_int(&v[i], &v[j]) /*@ where (neq) x = l_v[i], y = l_v[j] */;
			swap_int(&w[i], &w[j]) /*@ where (neq) x = l_w[i], y = l_w[j] */;
		} else {
			/*@ Assert
				u == u@pre && v == v@pre && w == w@pre &&
				i == i@pre && j == j@pre &&
				0 <= j && j < i && i < n &&
				Zlength(l_u) == n && Zlength(l_v) == n && Zlength(l_w) == n &&
				IntArray::seg(u, 0, i, sublist(0, i, l_u)) *
				IntArray::seg(u, i, n, sublist(i, n, l_u)) *
				IntArray::seg(v, 0, i, sublist(0, i, l_v)) *
				IntArray::seg(v, i, n, sublist(i, n, l_v)) *
				IntArray::seg(w, 0, i, sublist(0, i, l_w)) *
				IntArray::seg(w, i, n, sublist(i, n, l_w))
			*/
			swap_int(&u[i], &u[j]) /*@ where (neq) x = l_u[i], y = l_u[j] */;
			swap_int(&v[i], &v[j]) /*@ where (neq) x = l_v[i], y = l_v[j] */;
			swap_int(&w[i], &w[j]) /*@ where (neq) x = l_w[i], y = l_w[j] */;
		}
	}
}

int partitionByWeight(int* u, int* v, int* w, int left, int right)
/*@ With orig_u orig_v orig_w edge_order l_u l_v l_w n
    Require 0 <= n && n <= INT_MAX &&
            0 <= left && left <= right && right < n &&
			edge_arrays_ordered_by(n, orig_u, orig_v, orig_w, l_u, l_v, l_w, edge_order) &&
			IntArray::full(u, n, l_u) *
			IntArray::full(v, n, l_v) *
			IntArray::full(w, n, l_w)
	Ensure u == u@pre && v == v@pre && w == w@pre &&
			left == left@pre && right == right@pre &&
			0 <= n && n <= INT_MAX &&
			left <= __return && __return <= right &&
			exists l_u1 l_v1 l_w1 edge_order1,
				edge_arrays_ordered_by(n, orig_u, orig_v, orig_w, l_u1, l_v1, l_w1, edge_order1) &&
				Permutation(edge_order, edge_order1) &&
				same_outside_edge_arrays_range(l_u, l_v, l_w, edge_order,
					l_u1, l_v1, l_w1, edge_order1, left, right) &&
				edge_arrays_partitioned_by_weight_at(l_w1, left, right, __return) &&
				IntArray::full(u, n, l_u1) *
				IntArray::full(v, n, l_v1) *
				IntArray::full(w, n, l_w1)
*/
{
	int pivot_w = w[right];
	int i = left;

	/*@ Inv Assert
		exists l_u1 l_v1 l_w1 edge_order1,
			u == u@pre && v == v@pre && w == w@pre &&
			left == left@pre && right == right@pre &&
			pivot_w == l_w[right] &&
			0 <= n && n <= INT_MAX &&
			0 <= left && left <= right && right < n &&
			left <= i && i <= j && j <= right &&
			edge_arrays_ordered_by(n, orig_u, orig_v, orig_w, l_u1, l_v1, l_w1, edge_order1) &&
			Permutation(edge_order, edge_order1) &&
			same_outside_edge_arrays_range(l_u, l_v, l_w, edge_order,
				l_u1, l_v1, l_w1, edge_order1, left, right) &&
			(forall k, left <= k && k < i =>
				l_w1[k] < pivot_w) &&
			(forall k, i <= k && k < j =>
				pivot_w <= l_w1[k]) &&
			l_w1[right] == pivot_w &&
			IntArray::full(u, n, l_u1) *
			IntArray::full(v, n, l_v1) *
			IntArray::full(w, n, l_w1)
		by array_length
	*/
	for (int j = left; j < right; j++) {
		if (w[j] < pivot_w) {
			swap_edge(u, v, w, i, j)
				/*@ where n = n */;
			i++;
		}
	}

	swap_edge(u, v, w, i, right)
		/*@ where n = n */;
	return i;
}

void quickByWeightRange(int* u, int* v, int* w, int left, int right)
/*@ With orig_u orig_v orig_w edge_order l_u l_v l_w n
	Require 0 <= n && n <= INT_MAX &&
			0 <= left && -1 <= right && right < n &&
			edge_arrays_ordered_by(n, orig_u, orig_v, orig_w, l_u, l_v, l_w, edge_order) &&
			IntArray::full(u, n, l_u) *
			IntArray::full(v, n, l_v) *
			IntArray::full(w, n, l_w)
	Ensure u == u@pre && v == v@pre && w == w@pre &&
			left == left@pre && right == right@pre &&
			0 <= n && n <= INT_MAX &&
			exists l_u1 l_v1 l_w1 edge_order1,
			edge_arrays_ordered_by(n, orig_u, orig_v, orig_w, l_u1, l_v1, l_w1, edge_order1) &&
			Permutation(edge_order, edge_order1) &&
			same_outside_edge_arrays_range(l_u, l_v, l_w, edge_order,
				l_u1, l_v1, l_w1, edge_order1, left, right) &&
			edge_arrays_range_sorted_by_weight(l_w1, left, right) &&
			IntArray::full(u, n, l_u1) *
			IntArray::full(v, n, l_v1) *
			IntArray::full(w, n, l_w1)
*/
{
	if (left < right) {
		int pivot = partitionByWeight(u, v, w, left, right);
		quickByWeightRange(u, v, w, left, pivot - 1);
		quickByWeightRange(u, v, w, pivot + 1, right);
	}
}

void quickByWeight(int* u, int* v, int* w, int n)
/*@ With orig_u orig_v orig_w edge_order l_u l_v l_w
	Require 0 <= n && n <= INT_MAX &&
			edge_arrays_ordered_by(n, orig_u, orig_v, orig_w, l_u, l_v, l_w, edge_order) &&
			IntArray::full(u, n, l_u) *
			IntArray::full(v, n, l_v) *
			IntArray::full(w, n, l_w)
	Ensure u == u@pre && v == v@pre && w == w@pre && n == n@pre &&
			0 <= n && n <= INT_MAX &&
			exists l_u1 l_v1 l_w1 edge_order1,
			after_sorted_edge_of_input(n, orig_u, orig_v, orig_w, l_u1, l_v1, l_w1, edge_order1) &&
			Permutation(edge_order, edge_order1) &&
			IntArray::full(u, n, l_u1) *
			IntArray::full(v, n, l_v1) *
			IntArray::full(w, n, l_w1)
*/
{
	if (n > 0) {
		quickByWeightRange(u, v, w, 0, n - 1);
	}
}

struct mst_tree* kruskal(int*u, int* v, int* w, int n, int m)
/*@ high_level_spec <= low_level_spec
	With orig_u orig_v orig_w (g : G)
		Require 2 <= n && n < INT_MAX &&
				1 <= m && m < INT_MAX &&
				array_graph(n, m, orig_u, orig_v, orig_w, g) &&
				KruskalEnv(g) &&
				edge_arrays_ordered_by(m, orig_u, orig_v, orig_w,
				orig_u, orig_v, orig_w, Zrange(0, m)) &&
			IntArray::full(u, m, orig_u) *
			IntArray::full(v, m, orig_v) *
			IntArray::full(w, m, orig_w)
		Ensure exists l_u l_v l_w edge_order lru lrv lrw rg,
				return_is_mst(g, rg) &&
				after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
					l_u, l_v, l_w, edge_order) &&
				kruskal_result_graph_matches_array(lru, lrv, lrw, g, rg) &&
				__return != 0 &&
				IntArray::full(u, m, l_u) *
				IntArray::full(v, m, l_v) *
				IntArray::full(w, m, l_w) *
				IntArray::full(__return -> ru, n - 1, lru) *
			IntArray::full(__return -> rv, n - 1, lrv) *
			IntArray::full(__return -> rw, n - 1, lrw)
*/
;

struct mst_tree* kruskal(int*u, int* v, int* w, int n, int m)
/*@ low_level_spec
	With orig_u orig_v orig_w (g : G) X
		Require 2 <= n && n < INT_MAX &&
				1 <= m && m < INT_MAX &&
				array_graph(n, m, orig_u, orig_v, orig_w, g) &&
				KruskalEnv(g) &&
				edge_arrays_ordered_by(m, orig_u, orig_v, orig_w,
				orig_u, orig_v, orig_w, Zrange(0, m)) &&
			safeExec(initStPred(g), KruskalProg(g), X) &&
			IntArray::full(u, m, orig_u) *
			IntArray::full(v, m, orig_v) *
			IntArray::full(w, m, orig_w)
		Ensure exists l_u l_v l_w edge_order lru lrv lrw rg,
				safeExec(kruskal_state_graph_matches(rg), return(tt), X) &&
				after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
					l_u, l_v, l_w, edge_order) &&
				kruskal_result_graph_matches_array(lru, lrv, lrw, g, rg) &&
				__return != 0 &&
				IntArray::full(u, m, l_u) *
				IntArray::full(v, m, l_v) *
				IntArray::full(w, m, l_w) *
				IntArray::full(__return -> ru, n - 1, lru) *
			IntArray::full(__return -> rv, n - 1, lrv) *
			IntArray::full(__return -> rw, n - 1, lrw)
*/
{
	quickByWeight(u, v, w, m)
		/*@ where orig_u = orig_u, orig_v = orig_v, orig_w = orig_w,
			  edge_order = Zrange(0, m), l_u = orig_u, l_v = orig_v, l_w = orig_w */;


	struct union_find* uf = uf_create(n);


	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_w = malloc_int_array(n - 1);

	int chosen = 0;
	int i = 0;
	/*@ Inv Assert
		exists l_u l_v l_w edge_order
			   l_out_u l_out_v l_out_w
			   (s : St) (repr_of : Z -> Z),
			0 <= i && i <= m &&
				0 <= chosen && chosen <= n - 1 &&
				u == u@pre && v == v@pre && w == w@pre &&
				n == n@pre && m == m@pre &&
				2 <= n && n < INT_MAX && 1 <= m && m < INT_MAX &&
				array_graph(n, m, orig_u, orig_v, orig_w, g) &&
				KruskalEnv(g) &&
				after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
					l_u, l_v, l_w, edge_order) &&
			kruskal_scan_state(g, edge_order, i, chosen, s) &&
			kruskal_scan_phase(g, s, chosen) &&
			union_find_connectivity_matches_state(g, s, repr_of) &&
			output_prefix_matches_state(g, chosen,
				l_out_u, l_out_v, l_out_w, s) &&
			safeExec(kruskal_state_is(s), KruskalProg(g), X) &&
			UF(uf, n, repr_of) *
			IntArray::full(u, m, l_u) *
			IntArray::full(v, m, l_v) *
			IntArray::full(w, m, l_w) *
			IntArray::seg(out_u, 0, chosen, l_out_u) *
			IntArray::undef_seg(out_u, chosen, n - 1) *
			IntArray::seg(out_v, 0, chosen, l_out_v) *
			IntArray::undef_seg(out_v, chosen, n - 1) *
			IntArray::seg(out_w, 0, chosen, l_out_w) *
			IntArray::undef_seg(out_w, chosen, n - 1)
		by array_length
	*/
	for (; i < m && chosen < n - 1; i++) {
		int edge_u = u[i];
		int edge_v = v[i];
		int edge_w = w[i];

		int root_u = uf_find(uf, edge_u)
			/*@ where n = n */;

		int root_v = uf_find(uf, edge_v)
			/*@ where n = n */;
		/*@ Assert
			exists l_u l_v l_w edge_order
				   l_out_u l_out_v l_out_w
				   (s : St) (repr_of : Z -> Z),
				0 <= i && i < m &&
				0 <= chosen && chosen <= n - 1 &&
				chosen < n - 1 &&
				edge_u == l_u[i] && edge_v == l_v[i] && edge_w == l_w[i] &&
				0 <= edge_u && edge_u < n &&
				0 <= edge_v && edge_v < n &&
				0 <= root_u && root_u < n &&
				0 <= root_v && root_v < n &&
				root_u == repr_of(edge_u) &&
				root_v == repr_of(edge_v) &&
				u == u@pre && v == v@pre && w == w@pre &&
				n == n@pre && m == m@pre &&
				2 <= n && n < INT_MAX && 1 <= m && m < INT_MAX &&
				array_graph(n, m, orig_u, orig_v, orig_w, g) &&
				KruskalEnv(g) &&
				after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
					l_u, l_v, l_w, edge_order) &&
				kruskal_scan_state(g, edge_order, i, chosen, s) &&
				kruskal_scan_phase(g, s, chosen) &&
				union_find_connectivity_matches_state(g, s, repr_of) &&
				output_prefix_matches_state(g, chosen,
					l_out_u, l_out_v, l_out_w, s) &&
				safeExec(kruskal_state_is(s), KruskalProg(g), X) &&
				UF(uf, n, repr_of) *
				IntArray::full(u, m, l_u) *
				IntArray::full(v, m, l_v) *
				IntArray::full(w, m, l_w) *
				IntArray::seg(out_u, 0, chosen, l_out_u) *
				IntArray::undef_seg(out_u, chosen, n - 1) *
				IntArray::seg(out_v, 0, chosen, l_out_v) *
				IntArray::undef_seg(out_v, chosen, n - 1) *
				IntArray::seg(out_w, 0, chosen, l_out_w) *
				IntArray::undef_seg(out_w, chosen, n - 1)
		*/

		if (root_u != root_v) {
			out_u[chosen] = edge_u;
			out_v[chosen] = edge_v;
			out_w[chosen] = edge_w;
			chosen++;
			uf_union(uf, edge_u, edge_v)
				/*@ where n = n */;
			/*@ Assert
				exists l_u l_v l_w edge_order
					   l_out_u l_out_v l_out_w
					   l_out_u1 l_out_v1 l_out_w1
					   (s : St) (s_next : St)
					   (repr_of : Z -> Z) (repr_of1 : Z -> Z) e,
					0 <= i && i < m &&
					1 <= chosen && chosen <= n - 1 &&
					root_u != root_v &&
					edge_u == l_u[i] && edge_v == l_v[i] && edge_w == l_w[i] &&
					0 <= edge_u && edge_u < n &&
					0 <= edge_v && edge_v < n &&
					0 <= root_u && root_u < n &&
					0 <= root_v && root_v < n &&
					root_u == repr_of(edge_u) &&
					root_v == repr_of(edge_v) &&
					u == u@pre && v == v@pre && w == w@pre &&
					n == n@pre && m == m@pre &&
					2 <= n && n < INT_MAX && 1 <= m && m < INT_MAX &&
					array_graph(n, m, orig_u, orig_v, orig_w, g) &&
					KruskalEnv(g) &&
					after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
						l_u, l_v, l_w, edge_order) &&
					kruskal_scan_state(g, edge_order, i, chosen - 1, s) &&
					kruskal_scan_phase(g, s, chosen - 1) &&
					union_find_connectivity_matches_state(g, s, repr_of) &&
					output_prefix_matches_state(g, chosen - 1,
						l_out_u, l_out_v, l_out_w, s) &&
					uf_different_class(repr_of, edge_u, edge_v) &&
					selected_edge_is_min_edge(g, edge_order, i, s, e) &&
					selected_edge_pair(g, e, edge_u, edge_v) &&
					selected_edge_add_to_mst(s, s_next, edge_u, edge_v, e) &&
					uf_merge(n, repr_of, edge_u, edge_v, repr_of1) &&
					kruskal_scan_state(g, edge_order, i + 1, chosen, s_next) &&
					kruskal_scan_phase(g, s_next, chosen) &&
					union_find_connectivity_matches_state(g, s_next, repr_of1) &&
					output_prefix_matches_state(g, chosen,
						l_out_u1, l_out_v1, l_out_w1, s_next) &&
					safeExec(kruskal_state_is(s_next), KruskalProg(g), X) &&
					UF(uf, n, repr_of1) *
					IntArray::full(u, m, l_u) *
					IntArray::full(v, m, l_v) *
					IntArray::full(w, m, l_w) *
					IntArray::seg(out_u, 0, chosen, l_out_u1) *
					IntArray::undef_seg(out_u, chosen, n - 1) *
					IntArray::seg(out_v, 0, chosen, l_out_v1) *
					IntArray::undef_seg(out_v, chosen, n - 1) *
					IntArray::seg(out_w, 0, chosen, l_out_w1) *
					IntArray::undef_seg(out_w, chosen, n - 1)
			*/
		} else {
			/*@ Assert
				exists l_u l_v l_w edge_order
					   l_out_u l_out_v l_out_w
					   (s : St) (repr_of : Z -> Z),
					0 <= i && i < m &&
					0 <= chosen && chosen <= n - 1 &&
					root_u == root_v &&
					edge_u == l_u[i] && edge_v == l_v[i] && edge_w == l_w[i] &&
					0 <= edge_u && edge_u < n &&
					0 <= edge_v && edge_v < n &&
					0 <= root_u && root_u < n &&
					0 <= root_v && root_v < n &&
					root_u == repr_of(edge_u) &&
					root_v == repr_of(edge_v) &&
					u == u@pre && v == v@pre && w == w@pre &&
					n == n@pre && m == m@pre &&
					2 <= n && n < INT_MAX && 1 <= m && m < INT_MAX &&
					array_graph(n, m, orig_u, orig_v, orig_w, g) &&
					KruskalEnv(g) &&
					after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
						l_u, l_v, l_w, edge_order) &&
					kruskal_scan_state(g, edge_order, i, chosen, s) &&
					kruskal_scan_phase(g, s, chosen) &&
					union_find_connectivity_matches_state(g, s, repr_of) &&
					output_prefix_matches_state(g, chosen,
						l_out_u, l_out_v, l_out_w, s) &&
					uf_same_class(repr_of, edge_u, edge_v) &&
					kruskal_scan_state(g, edge_order, i + 1, chosen, s) &&
					safeExec(kruskal_state_is(s), KruskalProg(g), X) &&
					UF(uf, n, repr_of) *
					IntArray::full(u, m, l_u) *
					IntArray::full(v, m, l_v) *
					IntArray::full(w, m, l_w) *
					IntArray::seg(out_u, 0, chosen, l_out_u) *
					IntArray::undef_seg(out_u, chosen, n - 1) *
					IntArray::seg(out_v, 0, chosen, l_out_v) *
					IntArray::undef_seg(out_v, chosen, n - 1) *
					IntArray::seg(out_w, 0, chosen, l_out_w) *
					IntArray::undef_seg(out_w, chosen, n - 1)
			*/
		}
		/*@ Assert
				exists l_u l_v l_w edge_order
					   l_out_u l_out_v l_out_w
					   (s_after : St) (repr_of_after : Z -> Z),
						0 <= i && i < m &&
						0 <= chosen && chosen <= n - 1 &&
						edge_u == l_u[i] && edge_v == l_v[i] && edge_w == l_w[i] &&
						0 <= edge_u && edge_u < n &&
						0 <= edge_v && edge_v < n &&
						0 <= root_u && root_u < n &&
						0 <= root_v && root_v < n &&
						u == u@pre && v == v@pre && w == w@pre &&
					n == n@pre && m == m@pre &&
					2 <= n && n < INT_MAX && 1 <= m && m < INT_MAX &&
					array_graph(n, m, orig_u, orig_v, orig_w, g) &&
					KruskalEnv(g) &&
					after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
						l_u, l_v, l_w, edge_order) &&
					kruskal_scan_state(g, edge_order, i + 1, chosen, s_after) &&
					kruskal_scan_phase(g, s_after, chosen) &&
					union_find_connectivity_matches_state(g, s_after, repr_of_after) &&
					output_prefix_matches_state(g, chosen,
						l_out_u, l_out_v, l_out_w, s_after) &&
					safeExec(kruskal_state_is(s_after), KruskalProg(g), X) &&
					UF(uf, n, repr_of_after) *
					IntArray::full(u, m, l_u) *
					IntArray::full(v, m, l_v) *
					IntArray::full(w, m, l_w) *
					IntArray::seg(out_u, 0, chosen, l_out_u) *
					IntArray::undef_seg(out_u, chosen, n - 1) *
					IntArray::seg(out_v, 0, chosen, l_out_v) *
					IntArray::undef_seg(out_v, chosen, n - 1) *
					IntArray::seg(out_w, 0, chosen, l_out_w) *
					IntArray::undef_seg(out_w, chosen, n - 1)
			*/
		}

	uf_free(uf) /*@ where n = n */;

	struct mst_tree* result = malloc_mst_tree();
	result->ru = out_u;
	result->rv = out_v;
	result->rw = out_w;
	return result;

}
