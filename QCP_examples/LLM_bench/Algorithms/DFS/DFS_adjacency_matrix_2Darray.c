#include "safeexec_def.h"
#include "int_ptr_array2_def.h"

/*@ Import Coq Require Import Algorithms.DFS.DFS */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_matrix_2Darray_lib */
/*@ Import Coq Import ZSimpleGraph */

/*@ Extern Coq (G :: *) */
/*@ Extern Coq
      (DFSAdjacencyMatrix2Darray::dfs_program :
        G -> Z -> program (Z -> Prop) unit)
      (DFSAdjacencyMatrix2Darray::dfs_loop :
        G -> Z -> program (Z -> Prop) unit)
      (eq :
        {A} -> A -> A -> Prop)
      (DFSAdjacencyMatrix2Darray::graph_reachable :
        G -> Z -> Z -> Prop)
      (DFSAdjacencyMatrix2Darray::dfs_continue :
        G -> Z -> unit -> program (Z -> Prop) unit)
      (DFSAdjacencyMatrix2Darray::processed_neighbors :
        G -> Z -> Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::visited_extension :
        (Z -> Prop) -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::empty_visited :
        (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::adjacency_matrix_model :
        G -> list (list Z) -> Prop)
      (ZSimpleGraph::vertex_count : G -> Z)
      (ZSimpleGraph::vertex_valid : G -> Z -> Prop)
      (ZSimpleGraph::graph_step : G -> Z -> Z -> Prop)
      (ZSimpleGraph::visited_values :
        G -> list Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::graph_rep :
        Z -> G -> list (list Z) -> Assertion)
      (DFSAdjacencyMatrix2Darray::graph : Z -> G -> Assertion)
      (DFSAdjacencyMatrix2Darray::visited :
        Z -> G -> (Z -> Prop) -> Assertion)
 */

/*
 * Recursive depth-first search over an adjacency-matrix graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  The matrix is a
 * vertex_count-by-vertex_count integer pointer array.  A nonzero entry at
 * matrix[u][v] denotes an edge from u to v.  The matrix is read-only; visited
 * is supplied by the caller and is updated in place.
 */
void dfs_adjacency_matrix_2Darray(int **matrix, int vertex_count,
                                  int *visited, int vertex)
/*@ high_level_spec <= low_level_spec
    With (g: G) (initial_visited_set: Z -> Prop)
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      DFSAdjacencyMatrix2Darray::empty_visited(initial_visited_set) &&
      DFSAdjacencyMatrix2Darray::graph(matrix, g) *
      DFSAdjacencyMatrix2Darray::visited(visited, g, initial_visited_set)
    Ensure
      exists (high_visited_set: Z -> Prop),
        (forall (v: Z),
          high_visited_set(v) =>
            DFSAdjacencyMatrix2Darray::graph_reachable(g, vertex, v)) &&
        (forall (v: Z),
          DFSAdjacencyMatrix2Darray::graph_reachable(g, vertex, v) =>
            high_visited_set(v)) &&
        DFSAdjacencyMatrix2Darray::graph(matrix, g) *
        DFSAdjacencyMatrix2Darray::visited(visited, g, high_visited_set)
 */
;

void dfs_adjacency_matrix_2Darray(int **matrix, int vertex_count,
                                  int *visited, int vertex)
/*@ bind_spec <= low_level_spec
    With {B} (g: G) (rows: list (list Z))
         (visited_set: Z -> Prop)
         (c: unit -> program (Z -> Prop) B) X
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      safeExec(eq(visited_set),
        bind(DFSAdjacencyMatrix2Darray::dfs_program(g, vertex), c), X) &&
      DFSAdjacencyMatrix2Darray::graph_rep(matrix, g, rows) *
      DFSAdjacencyMatrix2Darray::visited(visited, g, visited_set)
    Ensure
      exists (bind_visited_set: Z -> Prop),
        DFSAdjacencyMatrix2Darray::visited_extension(
          visited_set, bind_visited_set) &&
        bind_visited_set(vertex) &&
        safeExec(eq(bind_visited_set), applyf(c, tt), X) &&
        DFSAdjacencyMatrix2Darray::graph_rep(matrix, g, rows) *
        DFSAdjacencyMatrix2Darray::visited(visited, g, bind_visited_set)
 */
;

void dfs_adjacency_matrix_2Darray(int **matrix, int vertex_count,
                                  int *visited, int vertex)
/*@ low_level_spec
    With (g: G) (rows: list (list Z))
         (visited_set: Z -> Prop) X
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      safeExec(eq(visited_set),
        DFSAdjacencyMatrix2Darray::dfs_program(g, vertex), X) &&
      DFSAdjacencyMatrix2Darray::graph_rep(matrix, g, rows) *
      DFSAdjacencyMatrix2Darray::visited(visited, g, visited_set)
    Ensure
      exists (low_visited_set: Z -> Prop),
        DFSAdjacencyMatrix2Darray::visited_extension(
          visited_set, low_visited_set) &&
        low_visited_set(vertex) &&
        safeExec(eq(low_visited_set), return(tt), X) &&
        DFSAdjacencyMatrix2Darray::graph_rep(matrix, g, rows) *
        DFSAdjacencyMatrix2Darray::visited(visited, g, low_visited_set)
 */
{
    /*@ Assert
          exists (values : list Z),
            matrix == matrix@pre && visited == visited@pre &&
            vertex_count == vertex_count@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count && vertex_count < INT_MAX &&
            0 <= vertex && vertex < vertex_count &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            safeExec(eq(visited_set),
              DFSAdjacencyMatrix2Darray::dfs_program(g, vertex), X) &&
            DFSAdjacencyMatrix2Darray::adjacency_matrix_model(g, rows) &&
            Zlength(Znth(vertex, rows, nil)) == vertex_count &&
            ZSimpleGraph::visited_values(g, values, visited_set) &&
            IntPtrArray2::full(matrix, vertex_count, rows) *
            IntArray::full(visited, vertex_count, values)
     */
    visited[vertex] = 1;

    /*@ Inv Assert
          exists (visited_set1 : Z -> Prop) (values1 : list Z),
            matrix == matrix@pre && visited == visited@pre &&
            vertex_count == vertex_count@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count && vertex_count < INT_MAX &&
            0 <= vertex && vertex < vertex_count &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            0 <= neighbor && neighbor <= vertex_count &&
            DFSAdjacencyMatrix2Darray::processed_neighbors(
              g, vertex, neighbor, visited_set1) &&
            DFSAdjacencyMatrix2Darray::visited_extension(
              visited_set, visited_set1) &&
            safeExec(eq(visited_set1),
              DFSAdjacencyMatrix2Darray::dfs_loop(g, vertex), X) &&
            DFSAdjacencyMatrix2Darray::adjacency_matrix_model(g, rows) &&
            Zlength(Znth(vertex, rows, nil)) == vertex_count &&
            ZSimpleGraph::visited_values(g, values1, visited_set1) &&
            IntPtrArray2::full(matrix, vertex_count, rows) *
            IntArray::full(visited, vertex_count, values1)
     */
    for (int neighbor = 0; neighbor < vertex_count; ++neighbor) {
        /*@ Assert
              exists (scan_visited_set : Z -> Prop) (scan_values : list Z)
                     (row_ptr : Z),
                matrix == matrix@pre && visited == visited@pre &&
                vertex_count == vertex_count@pre && vertex == vertex@pre &&
                vertex_count == ZSimpleGraph::vertex_count(g) &&
                0 < vertex_count && vertex_count < INT_MAX &&
                0 <= vertex && vertex < vertex_count &&
                0 <= neighbor && neighbor < vertex_count &&
                ZSimpleGraph::vertex_valid(g, vertex) &&
                DFSAdjacencyMatrix2Darray::processed_neighbors(
                  g, vertex, neighbor, scan_visited_set) &&
                DFSAdjacencyMatrix2Darray::visited_extension(
                  visited_set, scan_visited_set) &&
                safeExec(eq(scan_visited_set),
                  DFSAdjacencyMatrix2Darray::dfs_loop(g, vertex), X) &&
                DFSAdjacencyMatrix2Darray::adjacency_matrix_model(g, rows) &&
                ZSimpleGraph::visited_values(g, scan_values, scan_visited_set) &&
                Zlength(Znth(vertex, rows, nil)) == vertex_count &&
                IntPtrArray2::missing_i(
                  matrix, vertex_count, vertex, row_ptr, rows) *
                data_at(matrix + (vertex * sizeof(int *)), int *, row_ptr) *
                IntArray::full(
                  row_ptr, Zlength(Znth(vertex, rows, nil)),
                  Znth(vertex, rows, nil)) *
                IntArray::full(visited, vertex_count, scan_values)
         */
        int edge_exists = matrix[vertex][neighbor];

        /*@ Assert
              exists (scan_visited_set2 : Z -> Prop) (scan_values2 : list Z),
                matrix == matrix@pre && visited == visited@pre &&
                vertex_count == vertex_count@pre && vertex == vertex@pre &&
                vertex_count == ZSimpleGraph::vertex_count(g) &&
                0 < vertex_count && vertex_count < INT_MAX &&
                0 <= vertex && vertex < vertex_count &&
                0 <= neighbor && neighbor < vertex_count &&
                edge_exists == Znth(neighbor, Znth(vertex, rows, nil), 0) &&
                ZSimpleGraph::vertex_valid(g, vertex) &&
                DFSAdjacencyMatrix2Darray::processed_neighbors(
                  g, vertex, neighbor, scan_visited_set2) &&
                DFSAdjacencyMatrix2Darray::visited_extension(
                  visited_set, scan_visited_set2) &&
                safeExec(eq(scan_visited_set2),
                  DFSAdjacencyMatrix2Darray::dfs_loop(g, vertex), X) &&
                DFSAdjacencyMatrix2Darray::adjacency_matrix_model(g, rows) &&
                ZSimpleGraph::visited_values(g, scan_values2, scan_visited_set2) &&
                Zlength(Znth(vertex, rows, nil)) == vertex_count &&
                IntPtrArray2::full(matrix, vertex_count, rows) *
                IntArray::full(visited, vertex_count, scan_values2)
         */
        if (edge_exists != 0 && visited[neighbor] == 0) {
            /*@ Assert
                  exists (call_visited_set : Z -> Prop),
                    matrix == matrix@pre && visited == visited@pre &&
                    vertex_count == vertex_count@pre &&
                    vertex == vertex@pre &&
                    vertex_count == ZSimpleGraph::vertex_count(g) &&
                    0 < vertex_count && vertex_count < INT_MAX &&
                    0 <= vertex && vertex < vertex_count &&
                    0 <= neighbor && neighbor < vertex_count &&
                    edge_exists == Znth(neighbor, Znth(vertex, rows, nil), 0) &&
                    ZSimpleGraph::vertex_valid(g, vertex) &&
                    ZSimpleGraph::vertex_valid(g, neighbor) &&
                    ZSimpleGraph::graph_step(g, vertex, neighbor) &&
                    (! call_visited_set(neighbor)) &&
                    DFSAdjacencyMatrix2Darray::adjacency_matrix_model(g, rows) &&
                    Zlength(Znth(vertex, rows, nil)) == vertex_count &&
                    DFSAdjacencyMatrix2Darray::processed_neighbors(
                      g, vertex, neighbor, call_visited_set) &&
                    DFSAdjacencyMatrix2Darray::visited_extension(
                      visited_set, call_visited_set) &&
                    safeExec(eq(call_visited_set),
                      bind(DFSAdjacencyMatrix2Darray::dfs_program(g, neighbor),
                        DFSAdjacencyMatrix2Darray::dfs_continue(g, vertex)), X) &&
                    DFSAdjacencyMatrix2Darray::graph_rep(matrix, g, rows) *
                    DFSAdjacencyMatrix2Darray::visited(
                      visited, g, call_visited_set)
             */
            /*@ Given call_visited_set */
            dfs_adjacency_matrix_2Darray(matrix, vertex_count,
                                         visited, neighbor)
              /*@ where (bind_spec)
                    g = g, rows = rows, visited_set = call_visited_set,
                    c = DFSAdjacencyMatrix2Darray::dfs_continue(g, vertex),
                    X = X;
                    B = unit */;
        }

        /*@ Assert
              exists (visited_set2 : Z -> Prop) (values2 : list Z),
                matrix == matrix@pre && visited == visited@pre &&
                vertex_count == vertex_count@pre && vertex == vertex@pre &&
                vertex_count == ZSimpleGraph::vertex_count(g) &&
                0 < vertex_count && vertex_count < INT_MAX &&
                0 <= vertex && vertex < vertex_count &&
                0 <= neighbor && neighbor < vertex_count &&
                edge_exists == Znth(neighbor, Znth(vertex, rows, nil), 0) &&
                ZSimpleGraph::vertex_valid(g, vertex) &&
                DFSAdjacencyMatrix2Darray::processed_neighbors(
                  g, vertex, neighbor + 1, visited_set2) &&
                DFSAdjacencyMatrix2Darray::visited_extension(
                  visited_set, visited_set2) &&
                safeExec(eq(visited_set2),
                  DFSAdjacencyMatrix2Darray::dfs_loop(g, vertex), X) &&
                DFSAdjacencyMatrix2Darray::adjacency_matrix_model(g, rows) &&
                Zlength(Znth(vertex, rows, nil)) == vertex_count &&
                ZSimpleGraph::visited_values(g, values2, visited_set2) &&
                IntPtrArray2::full(matrix, vertex_count, rows) *
                IntArray::full(visited, vertex_count, values2)
         */
        /*@ Given visited_set2 values2 */
    }

    /*@ Assert
          exists (visited_set_out : Z -> Prop),
            matrix == matrix@pre && visited == visited@pre &&
            vertex_count == vertex_count@pre && vertex == vertex@pre &&
            DFSAdjacencyMatrix2Darray::visited_extension(
              visited_set, visited_set_out) &&
            visited_set_out(vertex) &&
            safeExec(eq(visited_set_out), return(tt), X) &&
            DFSAdjacencyMatrix2Darray::graph_rep(matrix, g, rows) *
            DFSAdjacencyMatrix2Darray::visited(visited, g, visited_set_out)
     */
}
