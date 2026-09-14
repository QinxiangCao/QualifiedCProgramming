#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_ptr_array2_def.h"
#include "graph_matrix_def.h"
#include "int_array_def.h"
#include "safeexec_def.h"

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Prim.prim_adjacency_matrix_lib */
/*@ Import Coq Require Import ListLib.Base.Positional */
/*@ Extern Coq (St :: *) */
/*@ Extern Coq V := Z */
/*@ Extern Coq (E :: *) */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq (Prim2: G -> program St unit) */
/*@ Extern Coq (Prim2_loop: G -> Z -> program St unit) */
/*@ Extern Coq (initSt: G -> V -> St) */
/*@ Extern Coq (initStPred: G -> V -> St -> Prop) */
/*@ Extern Coq (PrimEnv: G -> V -> Prop) */
/*@ Extern Coq (prim_adjacency_matrix_graph_model: Z -> G -> Z -> list (list Z) -> Prop) */
/*@ Extern Coq (prim_result_weight: G -> Z -> Prop) */
/*@ Extern Coq (prim_input_weight_bound: Z -> Z -> Prop) */
/*@ Extern Coq (prim_result_weight_in_int64_range: G -> Prop) */
/*@ Extern Coq (lowcost_prefix_sum: Z -> list Z -> Z) */
/*@ Extern Coq (lowcost_sum_matches_state: St -> list Z -> Prop) */
/*@ Extern Coq (lowcost_values_in_range: Z -> list Z -> Prop) */
/*@ Extern Coq (prim_state_is: St -> St -> Prop) */
/*@ Extern Coq (prim_state_graph_matches: G -> St -> Prop) */
/*@ Extern Coq (return_is_mst: G -> G -> Prop) */
/*@ Extern Coq (visited_matches_state: G -> St -> list Z -> Prop) */
/*@ Extern Coq (state_vertex_count: St -> Z) */
/*@ Extern Coq (growing_subgraph_state: G -> St -> Prop) */
/*@ Extern Coq (default_edge_list: Z -> list E) */
/*@ Extern Coq (lowcost_parent_match: G -> St -> list Z -> list E -> Z -> Prop) */
/*@ Extern Coq (selected_edges_match_state: G -> V -> St -> list E -> Prop) */
/*@ Extern Coq (candidate_vertex_exists_in_range: Z -> G -> St -> list Z -> list E -> Z -> Prop) */
/*@ Extern Coq (min_vertex_in_range: G -> St -> Z -> Z -> V -> list Z -> list E -> Prop) */
/*@ Extern Coq (selected_parent_edge_is_min_cut_edge: G -> St -> list E -> V -> Prop) */
/*@ Extern Coq (selected_parent_pair: G -> St -> list E -> V -> V -> V -> Prop) */
/*@ Extern Coq (selected_parent_add_to_mst: G -> St -> St -> list E -> V -> Prop) */
/*@ Extern Coq (scan_matrix_row_prefix_update: G -> list (list Z) -> Z -> St -> V -> Z -> list Z -> list E -> list Z -> list E -> Prop) */
/*@ Extern Coq (scan_matrix_row_full_update: Z -> G -> list (list Z) -> Z -> St -> V -> list Z -> list E -> list Z -> list E -> Prop) */

int* malloc_int_array(int n)
/*@ Require n > 0 && emp
    Ensure IntArray::undef_full(__return, n)
*/
;

void free_int_array(int *a)
/*@ With n l
    Require IntArray::full(a, n, l)
    Ensure emp
*/
;

long long prim_adjacency_matrix(int n, int** graph)
/*@ high_level_spec <= low_level_spec
    With (matrix: list (list Z)) (g: G) (src: V)
	    Require
	        src == 0 &&
	        2 <= n && n < INT_MAX &&
	        prim_input_weight_bound(n, 1000000000) &&
	        PrimEnv(g, src) &&

	        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix)
		    Ensure
		        exists rg,
		            return_is_mst(g, rg) &&
		            prim_result_weight(rg, __return) &&
		            prim_result_weight_in_int64_range(rg) &&

		            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix)
	*/
;

long long prim_adjacency_matrix(int n, int** graph)
/*@ low_level_spec
    With (matrix: list (list Z)) (g: G) (src: V) X
    Require
        src == 0 &&
        2 <= n && n < INT_MAX &&
        prim_input_weight_bound(n, 1000000000) &&
        PrimEnv(g, src) &&

        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
        safeExec(initStPred(g, src), Prim2(g), X)
    Ensure
        exists rg,
            safeExec(prim_state_graph_matches(rg), return(tt), X) &&
            prim_result_weight(rg, __return) &&
            prim_result_weight_in_int64_range(rg) &&

            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix)
*/
{
    int* visited = malloc_int_array(n);
    int i = 0;
   
   
    
	    /*@ Inv Assert
	        0 <= i && i <= n@pre &&
	       
	        
	        src == 0 &&
        
        n == n@pre &&
        graph == graph@pre &&
        2 <= n@pre && n@pre < INT_MAX &&
        prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&

        safeExec(initStPred(g, src), Prim2(g), X) &&

        IntArray::seg(visited, 0, i, repeat_Z(0, i)) *
        IntArray::undef_seg(visited, i, n@pre) *
        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix)
    */
    for (; i < n; i++) {
        visited[i] = 0;
    }

    int* lowcost = malloc_int_array(n);
    i = 0;
	    /*@ Inv Assert
	        0 <= i && i <= n@pre &&
	        
	        src == 0 &&
       
        n == n@pre &&
        graph == graph@pre &&
        2 <= n@pre && n@pre < INT_MAX &&
        prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&

        safeExec(initStPred(g, src), Prim2(g), X) &&

        IntArray::full(visited, n@pre, repeat_Z(0, n@pre)) *
        IntArray::seg(lowcost, 0, i, repeat_Z(1000000000, i)) *
        IntArray::undef_seg(lowcost, i, n@pre) *
        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix)
    */
    for (; i < n; i++) {
        lowcost[i] = 1000000000;
    }
    
	    /*@ Assert
	        src == 0 &&
	        i == n@pre &&
	        
	        n == n@pre &&
	        graph == graph@pre &&
        2 <= n@pre && n@pre < INT_MAX &&
        prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&

        safeExec(initStPred(g, src), Prim2(g), X) &&

        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
       IntArray::full(visited, n@pre, repeat_Z(0, n@pre)) *
        IntArray::full(lowcost, n@pre, repeat_Z(1000000000, n@pre))
    */
   
    lowcost[0] = 0;
    i = 0;
    
	    /*@ Inv
	        boot:
	            i == 0 &&
	            src == 0 &&
	            n == n@pre &&
	            graph == graph@pre &&
	            2 <= n@pre && n@pre < INT_MAX &&
	            prim_input_weight_bound(n@pre, 1000000000) &&
	            PrimEnv(g, src) &&

	            safeExec(initStPred(g, src), Prim2(g), X) &&

	            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
	            IntArray::full(visited, n@pre, repeat_Z(0, n@pre)) *
	            IntArray::full(lowcost, n@pre, replace_Znth(0, 0, repeat_Z(1000000000, n@pre)));
	        running:
	            exists l_visited l_lowcost l_edge_parent s,
	            1 <= i && i <= n@pre &&
	            src == 0 &&
	            n == n@pre &&
	            graph == graph@pre &&
	            2 <= n@pre && n@pre < INT_MAX &&
	            prim_input_weight_bound(n@pre, 1000000000) &&
	            PrimEnv(g, src) &&

	            growing_subgraph_state(g, s) &&
	            visited_matches_state(g, s, l_visited) &&
	            state_vertex_count(s) == i &&
	            selected_edges_match_state(g, src, s, l_edge_parent) &&
	            lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
	            lowcost_sum_matches_state(s, l_lowcost) &&
	            lowcost_values_in_range(1000000000, l_lowcost) &&
	            (i < n@pre => candidate_vertex_exists_in_range(n@pre, g, s, l_lowcost, l_edge_parent, 1000000000)) &&

	            safeExec(prim_state_is(s), Prim2_loop(g, i - 1), X) &&

	            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
	            IntArray::full(visited, n@pre, l_visited) *
	            IntArray::full(lowcost, n@pre, l_lowcost)
        with
        all ==> boot
        boot ==> running
        running ==> running
    */
    for (; i < n; i++) {
        int minIndex = -1;
        int min = 1000000000;
        int j = 0;
        /*@ Inv Assert
            exists l_visited l_lowcost l_edge_parent s,
            0 <= j && j <= n@pre &&
            0 <= i && i < n@pre &&
            src == 0 &&
            n == n@pre &&
            graph == graph@pre &&
            2 <= n@pre && n@pre < INT_MAX &&
            prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&
            INT_MIN <= min && min <= INT_MAX &&
            ((i == 0 &&

              safeExec(initStPred(g, src), Prim2(g), X) &&
              (j == 0 => min == 1000000000 && minIndex == -1) &&
              (1 <= j => min == 0 && minIndex == 0) &&
	              (minIndex != -1 => 0 <= minIndex && minIndex < j) &&
	              l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
	              lowcost_values_in_range(1000000000, l_lowcost) &&
	              l_edge_parent == default_edge_list(n@pre) &&
              l_visited == repeat_Z(0, n@pre))
             ||
             (1 <= i && i < n@pre &&

              safeExec(prim_state_is(s), Prim2_loop(g, i - 1), X) &&
              growing_subgraph_state(g, s) &&
              visited_matches_state(g, s, l_visited) &&
              state_vertex_count(s) == i &&
              selected_edges_match_state(g, src, s, l_edge_parent) &&
              lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
              lowcost_sum_matches_state(s, l_lowcost) &&
              lowcost_values_in_range(1000000000, l_lowcost) &&
              
              (i < n@pre => candidate_vertex_exists_in_range(n@pre, g, s, l_lowcost, l_edge_parent, 1000000000)) &&
              min_vertex_in_range(g, s, j, 1000000000, minIndex, l_lowcost, l_edge_parent) &&
              (minIndex == -1 => min == 1000000000) &&
              (minIndex != -1 => min == Znth(minIndex, l_lowcost, 0)) &&
              (minIndex != -1 => 0 <= minIndex && minIndex < j))) &&

	            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
	            IntArray::full(visited, n@pre, l_visited) *
	            IntArray::full(lowcost, n@pre, l_lowcost)
        */
        for (; j < n; j++) {
            if (visited[j] == 0 && lowcost[j] < min)  {
                min = lowcost[j];
                minIndex = j;
            }
        }
        /*@ Assert
            exists l_visited l_lowcost l_edge_parent s u v,
            j == n@pre &&
            0 <= i && i < n@pre &&
            0 <= minIndex && minIndex < n@pre &&
            src == 0 &&
            n == n@pre &&
            graph == graph@pre &&
            2 <= n@pre && n@pre < INT_MAX &&
            prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&
            INT_MIN <= min && min <= INT_MAX &&
		            ((i == 0 &&

		              safeExec(initStPred(g, src), Prim2(g), X) &&
		              min == 0 &&
		              minIndex == 0 &&
	              l_lowcost == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
	              lowcost_values_in_range(1000000000, l_lowcost) &&
	              l_edge_parent == default_edge_list(n@pre) &&
              l_visited == repeat_Z(0, n@pre))
             ||
             (1 <= i && i < n@pre &&

              safeExec(prim_state_is(s), Prim2_loop(g, i - 1), X) &&
              growing_subgraph_state(g, s) &&
              visited_matches_state(g, s, l_visited) &&
              state_vertex_count(s) == i &&
              selected_edges_match_state(g, src, s, l_edge_parent) &&
              lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
              lowcost_sum_matches_state(s, l_lowcost) &&
              lowcost_values_in_range(1000000000, l_lowcost) &&
		              candidate_vertex_exists_in_range(n@pre, g, s, l_lowcost, l_edge_parent, 1000000000) &&
	              minIndex != -1 &&
	              min == Znth(minIndex, l_lowcost, 0) &&
	              selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent, minIndex) &&
              selected_parent_pair(g, s, l_edge_parent, minIndex, u, v) &&
              min_vertex_in_range(g, s, n@pre, 1000000000, minIndex, l_lowcost, l_edge_parent))) &&

            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
            IntArray::full(visited, n@pre, l_visited) *
            IntArray::full(lowcost, n@pre, l_lowcost)
            */
        if (0 <= minIndex && minIndex < n) {
            visited[minIndex] = 1;
            /*@ Assert
                exists l_visited l_lowcost0 l_edge_parent0 s s_after u v row_ptr,
                j == n@pre &&
	                0 <= i && i < n@pre &&
	                0 <= minIndex && minIndex < n@pre &&
	                Zlength(Znth(minIndex, matrix, nil)) == n@pre &&
	                prim_adjacency_matrix_graph_model(n@pre, g, 1000000000, matrix) &&
	                graph == graph@pre &&
                n == n@pre &&
                src == 0 &&
                2 <= n@pre && n@pre < INT_MAX &&
                prim_input_weight_bound(n@pre, 1000000000) &&
	            PrimEnv(g, src) &&
                INT_MIN <= min && min <= INT_MAX &&
                ((i == 0 &&
                  minIndex == 0 &&
                  min == 0 &&
                  s_after == initSt(g, src) &&

                  safeExec(prim_state_is(s_after), Prim2_loop(g, 0), X) &&
                  growing_subgraph_state(g, s_after) &&
                  visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
                  state_vertex_count(s_after) == 1 &&
                  lowcost_sum_matches_state(s_after, l_lowcost0) &&
                  lowcost_values_in_range(1000000000, l_lowcost0) &&
                  l_lowcost0 == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
                  l_edge_parent0 == default_edge_list(n@pre) &&
                  l_visited == repeat_Z(0, n@pre))
                 ||
                 (1 <= i && i < n@pre &&
                  min == Znth(minIndex, l_lowcost0, 0) &&

                  safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&
                  growing_subgraph_state(g, s) &&
                  visited_matches_state(g, s, l_visited) &&
                  state_vertex_count(s) == i &&
                  selected_edges_match_state(g, src, s, l_edge_parent0) &&
                  lowcost_parent_match(g, s, l_lowcost0, l_edge_parent0, 1000000000) &&
                  lowcost_sum_matches_state(s, l_lowcost0) &&
                  lowcost_values_in_range(1000000000, l_lowcost0) &&
                  selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent0, minIndex) &&
                  selected_parent_pair(g, s, l_edge_parent0, minIndex, u, v) &&
                  selected_parent_add_to_mst(g, s, s_after, l_edge_parent0, minIndex) &&
                  growing_subgraph_state(g, s_after) &&
	                  visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
	                  state_vertex_count(s_after) == i + 1 &&
	                  selected_edges_match_state(g, src, s_after, l_edge_parent0) &&
	                  lowcost_sum_matches_state(s_after, l_lowcost0) &&
	                  lowcost_values_in_range(1000000000, l_lowcost0))) &&

                IntPtrArray2::missing_i(graph, n, minIndex, row_ptr, matrix) *
                data_at(graph + (minIndex * sizeof(int *)), int *, row_ptr) *
                IntArray::full(row_ptr, Zlength(Znth(minIndex, matrix, nil)), Znth(minIndex, matrix, nil)) *
                IntArray::full(visited, n@pre, replace_Znth(minIndex, 1, l_visited)) *
                IntArray::full(lowcost, n@pre, l_lowcost0)
            */
            int* selected_row = graph[minIndex];
            j = 0;
            /*@ Inv Assert
                exists l_visited l_lowcost0 l_lowcost l_edge_parent0 l_edge_parent s s_after u v row_ptr,
                0 <= j && j <= n@pre &&
	                0 <= i && i < n@pre &&
	                0 <= minIndex && minIndex < n@pre &&
	                Zlength(Znth(minIndex, matrix, nil)) == n@pre &&
	                prim_adjacency_matrix_graph_model(n@pre, g, 1000000000, matrix) &&
							            graph == graph@pre &&
	            n == n@pre &&
	            src == 0 &&
	            2 <= n@pre && n@pre < INT_MAX &&
                prim_input_weight_bound(n@pre, 1000000000) &&
	            PrimEnv(g, src) &&
                INT_MIN <= min && min <= INT_MAX &&
		        ((i == 0 &&
		                  minIndex == 0 &&
	                  min == 0 &&
	                  s_after == initSt(g, src) &&

                  safeExec(prim_state_is(s_after), Prim2_loop(g, 0), X) &&
                  growing_subgraph_state(g, s_after) &&
		                  visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
		                  state_vertex_count(s_after) == 1 &&
		                  lowcost_sum_matches_state(s_after, l_lowcost0) &&
		                  lowcost_values_in_range(1000000000, l_lowcost0) &&
		                  l_lowcost0 == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
	                  l_edge_parent0 == default_edge_list(n@pre) &&
	                  l_visited == repeat_Z(0, n@pre))
	                ||
	                 (1 <= i && i < n@pre &&
	                  min == Znth(minIndex, l_lowcost0, 0) &&

	                  safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&
                  growing_subgraph_state(g, s) &&
                  visited_matches_state(g, s, l_visited) &&
                  state_vertex_count(s) == i &&
                  selected_edges_match_state(g, src, s, l_edge_parent0) &&
                  lowcost_parent_match(g, s, l_lowcost0, l_edge_parent0, 1000000000) &&
                  selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent0, minIndex) &&
                  selected_parent_pair(g, s, l_edge_parent0, minIndex, u, v) &&
                  selected_parent_add_to_mst(g, s, s_after, l_edge_parent0, minIndex) &&
                  growing_subgraph_state(g, s_after) &&
	                  visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
	                  state_vertex_count(s_after) == i + 1 &&
					                  selected_edges_match_state(g, src, s_after, l_edge_parent0) &&
			                  lowcost_sum_matches_state(s_after, l_lowcost0) &&
			                  lowcost_values_in_range(1000000000, l_lowcost0))) &&
		                scan_matrix_row_prefix_update(g, matrix, 1000000000, s_after, minIndex, j,
		                  l_lowcost0, l_edge_parent0, l_lowcost, l_edge_parent) &&
		                lowcost_sum_matches_state(s_after, l_lowcost) &&
		                lowcost_values_in_range(1000000000, l_lowcost) &&
                0 <= j && j <= Zlength(Znth(minIndex, matrix, nil)) &&
                selected_row == row_ptr &&

                IntPtrArray2::missing_i(graph, n, minIndex, row_ptr, matrix) *
                data_at(graph + (minIndex * sizeof(int *)), int *, row_ptr) *
                IntArray::full(row_ptr, Zlength(Znth(minIndex, matrix, nil)), Znth(minIndex, matrix, nil)) *
                IntArray::full(visited, n@pre, replace_Znth(minIndex, 1, l_visited)) *
                IntArray::full(lowcost, n@pre, l_lowcost)
            */
            for (; j < n; j++) {
                /*@ Assert
                    exists l_visited l_lowcost0 l_lowcost l_edge_parent0 l_edge_parent s s_after u v row_ptr,
                    0 <= j && j < n@pre &&
                    0 <= j && j < n &&
                    0 <= j && j < Zlength(Znth(minIndex, matrix, nil)) &&
	                    0 <= i && i < n@pre &&
	                    0 <= minIndex && minIndex < n@pre &&
	                    Zlength(Znth(minIndex, matrix, nil)) == n@pre &&
	                    prim_adjacency_matrix_graph_model(n@pre, g, 1000000000, matrix) &&
	                    0 <= minIndex && minIndex < n &&
                    graph == graph@pre &&
                    n == n@pre &&
                    src == 0 &&
                    0 < n && n < INT_MAX &&
                    2 <= n@pre && n@pre < INT_MAX &&
                    prim_input_weight_bound(n@pre, 1000000000) &&
	            PrimEnv(g, src) &&
                    INT_MIN <= min && min <= INT_MAX &&
                    ((i == 0 &&
                      minIndex == 0 &&
                      min == 0 &&
                      s_after == initSt(g, src) &&

                      safeExec(prim_state_is(s_after), Prim2_loop(g, 0), X) &&
                      growing_subgraph_state(g, s_after) &&
	                      visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
	                      state_vertex_count(s_after) == 1 &&
	                      lowcost_sum_matches_state(s_after, l_lowcost0) &&
	                      lowcost_values_in_range(1000000000, l_lowcost0) &&
	                      l_lowcost0 == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
	                      l_edge_parent0 == default_edge_list(n@pre) &&
	                      l_visited == repeat_Z(0, n@pre))
                     ||
                     (1 <= i && i < n@pre &&
                      min == Znth(minIndex, l_lowcost0, 0) &&

                      safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&
                      growing_subgraph_state(g, s) &&
                      visited_matches_state(g, s, l_visited) &&
                      state_vertex_count(s) == i &&
                      selected_edges_match_state(g, src, s, l_edge_parent0) &&
                      lowcost_parent_match(g, s, l_lowcost0, l_edge_parent0, 1000000000) &&
                      selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent0, minIndex) &&
                      selected_parent_pair(g, s, l_edge_parent0, minIndex, u, v) &&
                      selected_parent_add_to_mst(g, s, s_after, l_edge_parent0, minIndex) &&
                      growing_subgraph_state(g, s_after) &&
	                          visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
		                          state_vertex_count(s_after) == i + 1 &&
		                          selected_edges_match_state(g, src, s_after, l_edge_parent0) &&
		                          lowcost_sum_matches_state(s_after, l_lowcost0) &&
		                          lowcost_values_in_range(1000000000, l_lowcost0))) &&
	                    scan_matrix_row_prefix_update(g, matrix, 1000000000, s_after, minIndex, j,
	                      l_lowcost0, l_edge_parent0, l_lowcost, l_edge_parent) &&
	                    lowcost_sum_matches_state(s_after, l_lowcost) &&
	                    lowcost_values_in_range(1000000000, l_lowcost) &&
                    selected_row == row_ptr &&

                    IntPtrArray2::missing_i(graph, n, minIndex, row_ptr, matrix) *
                    data_at(graph + (minIndex * sizeof(int *)), int *, row_ptr) *
                    IntArray::missing_i(selected_row, j, 0, Zlength(Znth(minIndex, matrix, nil)), Znth(minIndex, matrix, nil)) *
                    data_at(selected_row + (j * sizeof(int)), int, Znth(j, Znth(minIndex, matrix, nil), 0)) *
                    IntArray::full(visited, n@pre, replace_Znth(minIndex, 1, l_visited)) *
                    IntArray::full(lowcost, n@pre, l_lowcost)
                */
                int w = selected_row[j];
                if (w != 1000000000) {
                    /*@ Assert
                        exists l_visited l_lowcost0 l_lowcost l_edge_parent0 l_edge_parent s s_after u v,
                        w == Znth(j, Znth(minIndex, matrix, nil), 0) &&
	                        w != 1000000000 &&
	                        0 <= j && j < n@pre &&
	                        0 <= i && i < n@pre &&
	                        0 <= minIndex && minIndex < n@pre &&
	                        prim_adjacency_matrix_graph_model(n@pre, g, 1000000000, matrix) &&
	                        n == n@pre &&
                        graph == graph@pre &&
                        src == 0 &&
                        2 <= n@pre && n@pre < INT_MAX &&
                        prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&
	                ((i == 0 &&
	                  minIndex == 0 &&
	                  min == 0 &&
	                  s_after == initSt(g, src) &&

	                  safeExec(prim_state_is(s_after), Prim2_loop(g, 0), X) &&
                          growing_subgraph_state(g, s_after) &&
	                          visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
	                          state_vertex_count(s_after) == 1 &&
	                          lowcost_sum_matches_state(s_after, l_lowcost0) &&
	                          lowcost_values_in_range(1000000000, l_lowcost0) &&
	                          l_lowcost0 == replace_Znth(0, 0, repeat_Z(1000000000, n@pre)) &&
	                          l_edge_parent0 == default_edge_list(n@pre) &&
	                          l_visited == repeat_Z(0, n@pre))
	                 ||
	                 (1 <= i && i < n@pre &&
	                  min == Znth(minIndex, l_lowcost0, 0) &&

	                  safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&
                          growing_subgraph_state(g, s) &&
                          visited_matches_state(g, s, l_visited) &&
                          state_vertex_count(s) == i &&
                          selected_edges_match_state(g, src, s, l_edge_parent0) &&
                          lowcost_parent_match(g, s, l_lowcost0, l_edge_parent0, 1000000000) &&
                          selected_parent_edge_is_min_cut_edge(g, s, l_edge_parent0, minIndex) &&
                          selected_parent_pair(g, s, l_edge_parent0, minIndex, u, v) &&
                          selected_parent_add_to_mst(g, s, s_after, l_edge_parent0, minIndex) &&
                          growing_subgraph_state(g, s_after) &&
	                          visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
		                          state_vertex_count(s_after) == i + 1 &&
		                          selected_edges_match_state(g, src, s_after, l_edge_parent0) &&
		                          lowcost_sum_matches_state(s_after, l_lowcost0) &&
		                          lowcost_values_in_range(1000000000, l_lowcost0))) &&
	                        scan_matrix_row_prefix_update(g, matrix, 1000000000, s_after, minIndex, j,
	                          l_lowcost0, l_edge_parent0, l_lowcost, l_edge_parent) &&
	                        lowcost_sum_matches_state(s_after, l_lowcost) &&
	                        lowcost_values_in_range(1000000000, l_lowcost) &&

                        IntPtrArray2::missing_i(graph, n, minIndex, selected_row, matrix) *
                        data_at(graph + (minIndex * sizeof(int *)), int *, selected_row) *
                        IntArray::missing_i(selected_row, j, 0, Zlength(Znth(minIndex, matrix, nil)), Znth(minIndex, matrix, nil)) *
                        data_at(selected_row + (j * sizeof(int)), int, Znth(j, Znth(minIndex, matrix, nil), 0)) *
                        IntArray::missing_i(visited, j, 0, n@pre, replace_Znth(minIndex, 1, l_visited)) *
                        data_at(visited + (j * sizeof(int)), int, Znth(j, replace_Znth(minIndex, 1, l_visited), 0)) *
                        IntArray::missing_i(lowcost, j, 0, n@pre, l_lowcost) *
                        data_at(lowcost + (j * sizeof(int)), int, Znth(j, l_lowcost, 0))
                    */
                    if (visited[j] == 0) {
                        if (w < lowcost[j]) {
                            lowcost[j] = w;
                        }
                    }
                }
            }
            /*@ Assert
                exists l_visited l_lowcost0 l_lowcost l_edge_parent0 l_edge_parent s_after,
                j == n@pre &&
                0 <= i && i < n@pre &&
                0 <= minIndex && minIndex < n@pre &&
                graph == graph@pre &&
                n == n@pre &&
                src == 0 &&
                2 <= n@pre && n@pre < INT_MAX &&
                prim_input_weight_bound(n@pre, 1000000000) &&
                PrimEnv(g, src) &&
	                ((i == 0 && minIndex == 0) ||
	                 (1 <= i && i < n@pre)) &&
	                ((i == 0 => min == 0) &&
	                 (1 <= i && i < n@pre => min == Znth(minIndex, l_lowcost0, 0))) &&
	                INT_MIN <= min && min <= INT_MAX &&
	                growing_subgraph_state(g, s_after) &&
                visited_matches_state(g, s_after, replace_Znth(minIndex, 1, l_visited)) &&
	                state_vertex_count(s_after) == i + 1 &&
	                selected_edges_match_state(g, src, s_after, l_edge_parent) &&
	                scan_matrix_row_full_update(n@pre, g, matrix, 1000000000, s_after, minIndex, l_lowcost0, l_edge_parent0, l_lowcost, l_edge_parent) &&
	                lowcost_parent_match(g, s_after, l_lowcost, l_edge_parent, 1000000000) &&
	                lowcost_sum_matches_state(s_after, l_lowcost) &&
	                lowcost_values_in_range(1000000000, l_lowcost) &&

                safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&

                GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
                IntArray::full(visited, n@pre, replace_Znth(minIndex, 1, l_visited)) *
                data_at(&selected_row, selected_row) *
                IntArray::full(lowcost, n@pre, l_lowcost)
            */
        }
	        /*@ Assert
			            exists l_visited l_lowcost l_edge_parent s_after,
		            0 <= i && i < n@pre &&
		            j == n@pre &&
		            0 <= minIndex && minIndex < n@pre &&
			            ((i == 0 && minIndex == 0) ||
			             (1 <= i && i < n@pre)) &&
						            graph == graph@pre &&
	            n == n@pre &&
	            src == 0 &&
	            2 <= n@pre && n@pre < INT_MAX &&
            prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&
            INT_MIN <= min && min <= INT_MAX &&
            growing_subgraph_state(g, s_after) &&
            visited_matches_state(g, s_after, l_visited) &&
            state_vertex_count(s_after) == i + 1 &&
            selected_edges_match_state(g, src, s_after, l_edge_parent) &&
            lowcost_parent_match(g, s_after, l_lowcost, l_edge_parent, 1000000000) &&
            lowcost_sum_matches_state(s_after, l_lowcost) &&
            lowcost_values_in_range(1000000000, l_lowcost) &&

	            safeExec(prim_state_is(s_after), Prim2_loop(g, i), X) &&

	            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
	            IntArray::full(visited, n@pre, l_visited) *
	            IntArray::full(lowcost, n@pre, l_lowcost)
        */
        /*@ boot ==> running */
        
	    }
	    long long ret = 0;
	    i = 0;
		    /*@ Inv Assert
		        exists l_visited l_lowcost l_edge_parent s,
		        0 <= i && i <= n@pre &&
		        ret == lowcost_prefix_sum(i, l_lowcost) &&
	        src == 0 &&
	        n == n@pre &&
	        graph == graph@pre &&
        2 <= n@pre && n@pre < INT_MAX &&
	        prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&
	        growing_subgraph_state(g, s) &&
	        visited_matches_state(g, s, l_visited) &&
	        state_vertex_count(s) == n@pre &&
	        selected_edges_match_state(g, src, s, l_edge_parent) &&
	        lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
	        lowcost_sum_matches_state(s, l_lowcost) &&
	        lowcost_values_in_range(1000000000, l_lowcost) &&

	        safeExec(prim_state_is(s), return(tt), X) &&

	        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
	        IntArray::full(visited, n@pre, l_visited) *
	        IntArray::full(lowcost, n@pre, l_lowcost)
	    */
    for (; i < n; i++) {
        ret += lowcost[i];
    }
	    /*@ Assert
	        exists l_visited l_lowcost l_edge_parent s rg,
	        i == n@pre &&
	        ret == lowcost_prefix_sum(n@pre, l_lowcost) &&
        src == 0 &&
        n == n@pre &&
        graph == graph@pre &&
        2 <= n@pre && n@pre < INT_MAX &&
        prim_input_weight_bound(n@pre, 1000000000) &&
            PrimEnv(g, src) &&
        growing_subgraph_state(g, s) &&
        visited_matches_state(g, s, l_visited) &&
        state_vertex_count(s) == n@pre &&
        selected_edges_match_state(g, src, s, l_edge_parent) &&
        lowcost_parent_match(g, s, l_lowcost, l_edge_parent, 1000000000) &&
        lowcost_sum_matches_state(s, l_lowcost) &&
        lowcost_values_in_range(1000000000, l_lowcost) &&
        prim_state_graph_matches(rg, s) &&

        safeExec(prim_state_graph_matches(rg), return(tt), X) &&
        prim_result_weight(rg, ret) &&
        prim_result_weight_in_int64_range(rg) &&

        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
	        IntArray::full(visited, n@pre, l_visited) *
	        IntArray::full(lowcost, n@pre, l_lowcost)
	    */
    /*@ Given l_visited l_lowcost */
    free_int_array(visited) /*@ where n = n@pre, l = l_visited */;
    free_int_array(lowcost) /*@ where n = n@pre, l = l_lowcost */;
    return ret;
}
