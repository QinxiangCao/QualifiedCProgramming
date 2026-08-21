#include "safeexec_def.h"
#include "graph_matrix_def.h"

#define MAXN 10
#define INF 1000000000

/*@ Import Coq Require Import Algorithms.Floyd.Floyd*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Floyd.Floyd_adjacency_matrix_lib */
/*@ Import Coq Import FloydGraph */
/*@ Import Coq Import FloydAdjacencyMatrix2Darray */

/*@ Extern Coq (G :: *) */
/*@ Extern Coq (state :: *) */
/*@ Extern Coq
      (FloydAdjacencyMatrix2Darray::floyd_indexed_program :
        G -> Z -> program state unit)
      (FloydAdjacencyMatrix2Darray::floyd_k_from:
        G -> Z -> Z -> program state unit)
      (FloydAdjacencyMatrix2Darray::floyd_i_k_from:
        G -> Z -> Z -> Z -> program state unit)
      (FloydAdjacencyMatrix2Darray::floyd_j_i_k_from:
        G -> Z -> Z -> Z -> Z -> program state unit)
      (FloydAdjacencyMatrix2Darray::state_of_matrix:
        list (list Z) -> state)
      (FloydAdjacencyMatrix2Darray::state_model:
        list (list Z) -> state -> Prop)
      (FloydAdjacencyMatrix2Darray::graph_storage_size:
        G -> Z)
      (FloydAdjacencyMatrix2Darray::graph_matrix_model:
        G -> list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::matrix_storage_size:
        Z)
      (FloydAdjacencyMatrix2Darray::matrix_rows_model:
        list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::graph_has_size:
        G -> Z -> Prop)
      (FloydAdjacencyMatrix2Darray::matrix_shape:
        list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::matrix_values_safe:
        list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::floyd_init_matrix:
        G -> list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::floyd_shortest_matrix:
        G -> list (list Z) -> Prop)
      (eq: {A} -> A -> A -> Prop)
*/

void floyd_adjacency_matrix(int n, int *dist)
/*@ high_level_spec <= low_level_spec
    With (g: G) (dist0: list (list Z))
    Require
      FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
      FloydAdjacencyMatrix2Darray::floyd_init_matrix(g, dist0) &&
      GraphMatrixFlat::graph_rep(
        MAXN,
        FloydAdjacencyMatrix2Darray::graph_matrix_model(g),
        dist, dist0)
    Ensure
      exists (dist1: list (list Z)),
        FloydAdjacencyMatrix2Darray::floyd_shortest_matrix(g, dist1) &&
        GraphMatrixFlat::graph_rep(
          MAXN,
          FloydAdjacencyMatrix2Darray::matrix_rows_model,
          dist, dist1)
 */
;

void floyd_adjacency_matrix(int n, int *dist)
/*@ low_level_spec
    With (g: G) (dist0: list (list Z)) X
    Require
      FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
      safeExec(FloydAdjacencyMatrix2Darray::state_model(dist0), FloydAdjacencyMatrix2Darray::floyd_indexed_program(g, n), X) &&
      GraphMatrixFlat::graph_rep(
        MAXN,
        FloydAdjacencyMatrix2Darray::graph_matrix_model(g),
        dist, dist0)
    Ensure
      exists (dist1: list (list Z)),
        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist1), return (tt), X) &&
      GraphMatrixFlat::graph_rep(
        MAXN,
        FloydAdjacencyMatrix2Darray::matrix_rows_model,
        dist, dist1)
  */
{

    int k, i, j;

    /*@ Inv Assert
          exists (dist_k: list (list Z)),
            n == n@pre && dist == dist@pre &&
            FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
            0 <= n && n <= MAXN &&
            0 <= k && k <= n &&
            (forall (r: Z) (c: Z),
              (0 <= r && r < MAXN && 0 <= c && c < MAXN) =>
                (0 <= dist_k[r][c] && dist_k[r][c] <= INF)) &&
            safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_k),
            FloydAdjacencyMatrix2Darray::floyd_k_from(g, n, k), X) &&
            FloydAdjacencyMatrix2Darray::matrix_shape(dist_k) &&
            FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_k) &&
            GraphMatrixFlat::graph_rep(
              MAXN,
              FloydAdjacencyMatrix2Darray::matrix_rows_model,
              dist, dist_k) *
            has_int_permission(&i) *
            has_int_permission(&j)
    */
    for (k = 0; k < n; ++k) {

        /*@ Inv Assert
              exists (dist_i: list (list Z)),
                n == n@pre && dist == dist@pre &&
                FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                0 <= n && n <= MAXN &&
                0 <= k && k < n &&
                0 <= i && i <= n &&
                (forall (r: Z) (c: Z),
                  (0 <= r && r < MAXN && 0 <= c && c < MAXN) =>
                    (0 <= dist_i[r][c] && dist_i[r][c] <= INF)) &&
                safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_i),
                FloydAdjacencyMatrix2Darray::floyd_i_k_from(g, n, k, i), X) &&
                FloydAdjacencyMatrix2Darray::matrix_shape(dist_i) &&
                FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_i) &&
                GraphMatrixFlat::graph_rep(
                  MAXN,
                  FloydAdjacencyMatrix2Darray::matrix_rows_model,
                  dist, dist_i) *
                has_int_permission(&j)
        */

        for (i = 0; i < n; ++i) {

            /*@ Inv Assert
                  exists (dist_j: list (list Z)),
                    n == n@pre && dist == dist@pre &&
                    FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                    0 <= n && n <= MAXN &&
                    0 <= k && k < n &&
                    0 <= i && i < n &&
                    0 <= j && j <= n &&
                    (forall (r: Z) (c: Z),
                      (0 <= r && r < MAXN &&
                       0 <= c && c < MAXN) =>
                        (0 <= dist_j[r][c] &&
                         dist_j[r][c] <= INF)) &&
                    safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                    FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                    FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                    FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                    GraphMatrixFlat::graph_rep(
                      MAXN,
                      FloydAdjacencyMatrix2Darray::matrix_rows_model,
                      dist, dist_j)
            */

            for (j = 0; j < n; ++j) {
                if (dist[i * MAXN + k] < INF &&
                    dist[k * MAXN + j] < INF &&
                    dist[i * MAXN + k] + dist[k * MAXN + j] < dist[i * MAXN + j]) {
                    dist[i * MAXN + j] = dist[i * MAXN + k] + dist[k * MAXN + j];
                }
            }
        }
    }
}
