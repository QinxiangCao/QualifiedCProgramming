#include "safeexec_def.h"
#include "array2_def.h"
#include "graph_matrix_def.h"

/*@ Import Coq Require Import Algorithms.DFS.DFS */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_matrix_lib */
/*@ Import Coq Import ZSimpleGraph */

/*@ Extern Coq (G :: *) */
/*@ Extern Coq
      (DFSAdjacencyMatrix::dfs_program :
        G -> Z -> program (Z -> Prop) unit)
      (DFSAdjacencyMatrix::dfs_loop :
        G -> Z -> program (Z -> Prop) unit)
      (eq :
        {A} -> A -> A -> Prop)
      (DFSAdjacencyMatrix::graph_reachable :
        G -> Z -> Z -> Prop)
      (DFSAdjacencyMatrix::dfs_continue :
        G -> Z -> unit -> program (Z -> Prop) unit)
      (DFSAdjacencyMatrix::processed_neighbors :
        G -> Z -> Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::visited_extension :
        (Z -> Prop) -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::empty_visited :
        (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::adjacency_matrix_model :
        G -> list (list Z) -> Prop)
      (ZSimpleGraph::vertex_count : G -> Z)
      (ZSimpleGraph::vertex_valid : G -> Z -> Prop)
      (ZSimpleGraph::graph_step : G -> Z -> Z -> Prop)
      (ZSimpleGraph::visited_values :
        G -> list Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::visited :
        Z -> G -> (Z -> Prop) -> Assertion)
 */

/*
 * Recursive depth-first search over an adjacency-matrix graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  The matrix is a
 * vertex_count-by-vertex_count integer array stored in row-major order.  A
 * nonzero entry at (u, v) denotes an edge from u to v.  The matrix is
 * read-only; visited is supplied by the caller and is updated in place.
 */
void dfs_adjacency_matrix(int *matrix, int vertex_count,
                          int *visited, int vertex)
/*@ high_level_spec <= low_level_spec
    With (g: G) (initial_visited_set: Z -> Prop)
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count * vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      DFSAdjacencyMatrix::empty_visited(initial_visited_set) &&
      exists (rows: list (list Z)),
        GraphMatrixFlat::graph_rep(
          vertex_count,
          DFSAdjacencyMatrix::adjacency_matrix_model(g),
          matrix, rows) *
      DFSAdjacencyMatrix::visited(visited, g, initial_visited_set)
    Ensure
      exists (high_visited_set: Z -> Prop),
        (forall (v: Z),
          high_visited_set(v) => DFSAdjacencyMatrix::graph_reachable(g, vertex, v)) &&
        (forall (v: Z),
          DFSAdjacencyMatrix::graph_reachable(g, vertex, v) => high_visited_set(v)) &&
        exists (rows: list (list Z)),
          GraphMatrixFlat::graph_rep(
            vertex_count,
            DFSAdjacencyMatrix::adjacency_matrix_model(g),
            matrix, rows) *
        DFSAdjacencyMatrix::visited(visited, g, high_visited_set)
 */
;

void dfs_adjacency_matrix(int *matrix, int vertex_count,
                          int *visited, int vertex)
/*@ bind_spec <= low_level_spec
    With {B} (g: G) (rows: list (list Z))
         (visited_set: Z -> Prop)
         (c: unit -> program (Z -> Prop) B) X
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count * vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      safeExec(eq(visited_set),
        bind(DFSAdjacencyMatrix::dfs_program(g, vertex), c), X) &&
      GraphMatrixFlat::graph_rep(
        vertex_count,
        DFSAdjacencyMatrix::adjacency_matrix_model(g),
        matrix, rows) *
      DFSAdjacencyMatrix::visited(visited, g, visited_set)
    Ensure
      exists (bind_visited_set: Z -> Prop),
        DFSAdjacencyMatrix::visited_extension(
          visited_set, bind_visited_set) &&
        bind_visited_set(vertex) &&
        safeExec(eq(bind_visited_set), applyf(c, tt), X) &&
        GraphMatrixFlat::graph_rep(
          vertex_count,
          DFSAdjacencyMatrix::adjacency_matrix_model(g),
          matrix, rows) *
        DFSAdjacencyMatrix::visited(visited, g, bind_visited_set)
 */
;

void dfs_adjacency_matrix(int *matrix, int vertex_count,
                          int *visited, int vertex)
/*@ low_level_spec
    With (g: G) (rows: list (list Z))
         (visited_set: Z -> Prop) X
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count * vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      safeExec(eq(visited_set),
        DFSAdjacencyMatrix::dfs_program(g, vertex), X) &&
      GraphMatrixFlat::graph_rep(
        vertex_count,
        DFSAdjacencyMatrix::adjacency_matrix_model(g),
        matrix, rows) *
      DFSAdjacencyMatrix::visited(visited, g, visited_set)
    Ensure
      exists (low_visited_set: Z -> Prop),
        DFSAdjacencyMatrix::visited_extension(
          visited_set, low_visited_set) &&
        low_visited_set(vertex) &&
        safeExec(eq(low_visited_set), return(tt), X) &&
        GraphMatrixFlat::graph_rep(
          vertex_count,
          DFSAdjacencyMatrix::adjacency_matrix_model(g),
          matrix, rows) *
        DFSAdjacencyMatrix::visited(visited, g, low_visited_set)
 */
{
    /*@ Assert
          exists (values : list Z),
            matrix == matrix@pre && visited == visited@pre &&
            vertex_count == vertex_count@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count &&
            vertex_count * vertex_count < INT_MAX &&
            0 <= vertex && vertex < vertex_count &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            safeExec(eq(visited_set),
              DFSAdjacencyMatrix::dfs_program(g, vertex), X) &&
            ZSimpleGraph::visited_values(g, values, visited_set) &&
            GraphMatrixFlat::graph_rep(
              vertex_count,
              DFSAdjacencyMatrix::adjacency_matrix_model(g),
              matrix, rows) *
            IntArray::full(visited, vertex_count, values)
     */
    visited[vertex] = 1;

    /*@ Inv Assert
          exists (visited_set1 : Z -> Prop) (values1 : list Z),
            matrix == matrix@pre && visited == visited@pre &&
            vertex_count == vertex_count@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count &&
            vertex_count * vertex_count < INT_MAX &&
            0 <= vertex && vertex < vertex_count &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            0 <= neighbor && neighbor <= vertex_count &&
            DFSAdjacencyMatrix::processed_neighbors(
              g, vertex, neighbor, visited_set1) &&
            DFSAdjacencyMatrix::visited_extension(
              visited_set, visited_set1) &&
            safeExec(eq(visited_set1),
              DFSAdjacencyMatrix::dfs_loop(g, vertex), X) &&
            ZSimpleGraph::visited_values(g, values1, visited_set1) &&
            GraphMatrixFlat::graph_rep(
              vertex_count,
              DFSAdjacencyMatrix::adjacency_matrix_model(g),
              matrix, rows) *
            IntArray::full(visited, vertex_count, values1)
     */
    for (int neighbor = 0; neighbor < vertex_count; ++neighbor) {
        if (matrix[vertex * vertex_count + neighbor] != 0 &&
            visited[neighbor] == 0) {
            /*@ Assert
                  exists (call_visited_set : Z -> Prop),
                    matrix == matrix@pre && visited == visited@pre &&
                    vertex_count == vertex_count@pre &&
                    vertex == vertex@pre &&
                    vertex_count == ZSimpleGraph::vertex_count(g) &&
                    0 < vertex_count &&
                    vertex_count * vertex_count < INT_MAX &&
                    0 <= vertex && vertex < vertex_count &&
                    0 <= neighbor && neighbor < vertex_count &&
                    ZSimpleGraph::vertex_valid(g, vertex) &&
                    ZSimpleGraph::vertex_valid(g, neighbor) &&
                    ZSimpleGraph::graph_step(g, vertex, neighbor) &&
                    (! call_visited_set(neighbor)) &&
                    DFSAdjacencyMatrix::processed_neighbors(
                      g, vertex, neighbor, call_visited_set) &&
                    DFSAdjacencyMatrix::visited_extension(
                      visited_set, call_visited_set) &&
                    safeExec(eq(call_visited_set),
                      bind(DFSAdjacencyMatrix::dfs_program(g, neighbor),
                        DFSAdjacencyMatrix::dfs_continue(g, vertex)), X) &&
                    GraphMatrixFlat::graph_rep(
                      vertex_count,
                      DFSAdjacencyMatrix::adjacency_matrix_model(g),
                      matrix, rows) *
                    DFSAdjacencyMatrix::visited(
                      visited, g, call_visited_set)
             */
            /*@ Given call_visited_set */
            dfs_adjacency_matrix(matrix, vertex_count, visited, neighbor)
              /*@ where (bind_spec)
                    g = g, rows = rows, visited_set = call_visited_set,
                    c = DFSAdjacencyMatrix::dfs_continue(g, vertex), X = X;
                    B = unit */;
        }

        /*@ Assert
              exists (visited_set2 : Z -> Prop) (values2 : list Z),
                matrix == matrix@pre && visited == visited@pre &&
                vertex_count == vertex_count@pre && vertex == vertex@pre &&
                vertex_count == ZSimpleGraph::vertex_count(g) &&
                0 < vertex_count &&
                vertex_count * vertex_count < INT_MAX &&
                0 <= vertex && vertex < vertex_count &&
                0 <= neighbor && neighbor < vertex_count &&
                ZSimpleGraph::vertex_valid(g, vertex) &&
                DFSAdjacencyMatrix::processed_neighbors(
                  g, vertex, neighbor + 1, visited_set2) &&
                DFSAdjacencyMatrix::visited_extension(
                  visited_set, visited_set2) &&
                safeExec(eq(visited_set2),
                  DFSAdjacencyMatrix::dfs_loop(g, vertex), X) &&
                ZSimpleGraph::visited_values(g, values2, visited_set2) &&
                GraphMatrixFlat::graph_rep(
                  vertex_count,
                  DFSAdjacencyMatrix::adjacency_matrix_model(g),
                  matrix, rows) *
                IntArray::full(visited, vertex_count, values2)
         */
        /*@ Given visited_set2 values2 */
    }

    /*@ Assert
          exists (visited_set_out : Z -> Prop),
            matrix == matrix@pre && visited == visited@pre &&
            vertex_count == vertex_count@pre && vertex == vertex@pre &&
            DFSAdjacencyMatrix::visited_extension(
              visited_set, visited_set_out) &&
            visited_set_out(vertex) &&
            safeExec(eq(visited_set_out), return(tt), X) &&
            GraphMatrixFlat::graph_rep(
              vertex_count,
              DFSAdjacencyMatrix::adjacency_matrix_model(g),
              matrix, rows) *
            DFSAdjacencyMatrix::visited(visited, g, visited_set_out)
     */
}
