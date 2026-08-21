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

int *graph_matrix_ptr_row(int **dist, int index)
/*@ low_level_spec
    With (rows: list (list Z))
    Require
      0 <= index && index < MAXN &&
      GraphMatrixPtr::graph_rep(
        MAXN,
        FloydAdjacencyMatrix2Darray::matrix_rows_model,
        dist, rows)
    Ensure
      exists (row_ptr: Z),
        __return == row_ptr &&
        GraphMatrixPtr::row_rep(
          MAXN,
          FloydAdjacencyMatrix2Darray::matrix_rows_model,
          dist, index, row_ptr, rows)
 */
;

void floyd_adjacency_matrix_ptr(int n, int **dist)
/*@ high_level_spec <= low_level_spec
    With (g: G) (dist0: list (list Z))
    Require
      FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
      FloydAdjacencyMatrix2Darray::floyd_init_matrix(g, dist0) &&
      GraphMatrixPtr::graph_rep(
        MAXN,
        FloydAdjacencyMatrix2Darray::graph_matrix_model(g),
        dist, dist0)
    Ensure
      exists (dist1: list (list Z)),
        FloydAdjacencyMatrix2Darray::floyd_shortest_matrix(g, dist1) &&
        GraphMatrixPtr::graph_rep(
          MAXN,
          FloydAdjacencyMatrix2Darray::matrix_rows_model,
          dist, dist1)
 */
;

void floyd_adjacency_matrix_ptr(int n, int **dist)
/*@ low_level_spec
    With (g: G) (dist0: list (list Z)) X
    Require
      FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
      safeExec(FloydAdjacencyMatrix2Darray::state_model(dist0), FloydAdjacencyMatrix2Darray::floyd_indexed_program(g, n), X) &&
      GraphMatrixPtr::graph_rep(
        MAXN,
        FloydAdjacencyMatrix2Darray::graph_matrix_model(g),
        dist, dist0)
    Ensure
      exists (dist1: list (list Z)),
        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist1), return (tt), X) &&
      GraphMatrixPtr::graph_rep(
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
            GraphMatrixPtr::graph_rep(
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
                GraphMatrixPtr::graph_rep(
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
                    GraphMatrixPtr::graph_rep(
                      MAXN,
                      FloydAdjacencyMatrix2Darray::matrix_rows_model,
                      dist, dist_j)
            */

            for (j = 0; j < n; ++j) {
                int *row_k;
                int *row_i;
                int dkj;
                int dik;
                int dij;

                row_k = graph_matrix_ptr_row(dist, k);
                /*@ Assert
                      exists (dist_j: list (list Z)) (row_k_ptr : Z),
                        n == n@pre && dist == dist@pre &&
                        FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                        0 <= n && n <= MAXN &&
                        0 <= k && k < n &&
                        0 <= k && k < MAXN &&
                        0 <= i && i < n &&
                        0 <= i && i < MAXN &&
                        0 <= j && j < n &&
                        0 <= j && j < MAXN &&
                        Zlength(dist_j[i]) == MAXN &&
                        Zlength(dist_j[k]) == MAXN &&
                        0 <= j && j < Zlength(dist_j[k]) &&
                        (forall (r: Z) (c: Z),
                          (0 <= r && r < MAXN &&
                           0 <= c && c < MAXN) =>
                            (0 <= dist_j[r][c] &&
                             dist_j[r][c] <= INF)) &&
                        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                        FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                        FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                        FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                        GraphMatrixPtr::row_rep(
                          MAXN,
                          FloydAdjacencyMatrix2Darray::matrix_rows_model,
                          dist, k, row_k_ptr, dist_j) *
                        store(&row_k, int *, row_k_ptr) *
                        has_ptr_permission(&row_i) *
                        has_int_permission(&dkj) *
                        has_int_permission(&dik) *
                        has_int_permission(&dij)
                */
                dkj = row_k[j];
                /*@ Assert
                      exists (dist_j: list (list Z)) (row_k_ptr : Z),
                        n == n@pre && dist == dist@pre &&
                        FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                        0 <= n && n <= MAXN &&
                        0 <= k && k < n &&
                        0 <= k && k < MAXN &&
                        0 <= i && i < n &&
                        0 <= i && i < MAXN &&
                        0 <= j && j < n &&
                        0 <= j && j < MAXN &&
                        Zlength(dist_j[i]) == MAXN &&
                        Zlength(dist_j[k]) == MAXN &&
                        0 <= k && k < Zlength(dist_j[i]) &&
                        0 <= j && j < Zlength(dist_j[i]) &&
                        dkj == dist_j[k][j] &&
                        (forall (r: Z) (c: Z),
                          (0 <= r && r < MAXN &&
                           0 <= c && c < MAXN) =>
                            (0 <= dist_j[r][c] &&
                             dist_j[r][c] <= INF)) &&
                        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                        FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                        FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                        FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                        GraphMatrixPtr::graph_rep(
                          MAXN,
                          FloydAdjacencyMatrix2Darray::matrix_rows_model,
                          dist, dist_j) *
                        store(&row_k, int *, row_k_ptr) *
                        has_ptr_permission(&row_i) *
                        has_int_permission(&dik) *
                        has_int_permission(&dij)
                */

                row_i = graph_matrix_ptr_row(dist, i);
                /*@ Assert
                      exists (dist_j: list (list Z)) (row_k_ptr : Z) (row_i_ptr : Z),
                        n == n@pre && dist == dist@pre &&
                        FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                        0 <= n && n <= MAXN &&
                        0 <= k && k < n &&
                        0 <= k && k < MAXN &&
                        0 <= i && i < n &&
                        0 <= i && i < MAXN &&
                        0 <= j && j < n &&
                        0 <= j && j < MAXN &&
                        Zlength(dist_j[i]) == MAXN &&
                        Zlength(dist_j[k]) == MAXN &&
                        0 <= k && k < Zlength(dist_j[i]) &&
                        0 <= j && j < Zlength(dist_j[i]) &&
                        dkj == dist_j[k][j] &&
                        (forall (r: Z) (c: Z),
                          (0 <= r && r < MAXN &&
                           0 <= c && c < MAXN) =>
                            (0 <= dist_j[r][c] &&
                             dist_j[r][c] <= INF)) &&
                        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                        FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                        FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                        FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                        GraphMatrixPtr::row_rep(
                          MAXN,
                          FloydAdjacencyMatrix2Darray::matrix_rows_model,
                          dist, i, row_i_ptr, dist_j) *
                        store(&row_k, int *, row_k_ptr) *
                        store(&row_i, int *, row_i_ptr) *
                        has_int_permission(&dik) *
                        has_int_permission(&dij)
                */
                dik = row_i[k];
                /*@ Assert
                      exists (dist_j: list (list Z)) (row_k_ptr : Z) (row_i_ptr : Z),
                        n == n@pre && dist == dist@pre &&
                        FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                        0 <= n && n <= MAXN &&
                        0 <= k && k < n &&
                        0 <= k && k < MAXN &&
                        0 <= i && i < n &&
                        0 <= i && i < MAXN &&
                        0 <= j && j < n &&
                        0 <= j && j < MAXN &&
                        Zlength(dist_j[i]) == MAXN &&
                        Zlength(dist_j[k]) == MAXN &&
                        0 <= j && j < Zlength(dist_j[i]) &&
                        dkj == dist_j[k][j] &&
                        dik == dist_j[i][k] &&
                        (forall (r: Z) (c: Z),
                          (0 <= r && r < MAXN &&
                           0 <= c && c < MAXN) =>
                            (0 <= dist_j[r][c] &&
                             dist_j[r][c] <= INF)) &&
                        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                        FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                        FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                        FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                        GraphMatrixPtr::graph_rep(
                          MAXN,
                          FloydAdjacencyMatrix2Darray::matrix_rows_model,
                          dist, dist_j) *
                        store(&row_k, int *, row_k_ptr) *
                        store(&row_i, int *, row_i_ptr) *
                        has_int_permission(&dij)
                */
                row_i = graph_matrix_ptr_row(dist, i);
                /*@ Assert
                      exists (dist_j: list (list Z)) (row_k_ptr : Z) (row_i_ptr : Z),
                        n == n@pre && dist == dist@pre &&
                        FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                        0 <= n && n <= MAXN &&
                        0 <= k && k < n &&
                        0 <= k && k < MAXN &&
                        0 <= i && i < n &&
                        0 <= i && i < MAXN &&
                        0 <= j && j < n &&
                        0 <= j && j < MAXN &&
                        Zlength(dist_j[i]) == MAXN &&
                        Zlength(dist_j[k]) == MAXN &&
                        0 <= j && j < Zlength(dist_j[i]) &&
                        dkj == dist_j[k][j] &&
                        dik == dist_j[i][k] &&
                        (forall (r: Z) (c: Z),
                          (0 <= r && r < MAXN &&
                           0 <= c && c < MAXN) =>
                            (0 <= dist_j[r][c] &&
                             dist_j[r][c] <= INF)) &&
                        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                        FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                        FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                        FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                        GraphMatrixPtr::row_rep(
                          MAXN,
                          FloydAdjacencyMatrix2Darray::matrix_rows_model,
                          dist, i, row_i_ptr, dist_j) *
                        store(&row_k, int *, row_k_ptr) *
                        store(&row_i, int *, row_i_ptr) *
                        has_int_permission(&dij)
                */
                dij = row_i[j];
                /*@ Assert
                      exists (dist_j: list (list Z)) (row_k_ptr : Z) (row_i_ptr : Z),
                        n == n@pre && dist == dist@pre &&
                        FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                        0 <= n && n <= MAXN &&
                        0 <= k && k < n &&
                        0 <= k && k < MAXN &&
                        0 <= i && i < n &&
                        0 <= i && i < MAXN &&
                        0 <= j && j < n &&
                        0 <= j && j < MAXN &&
                        Zlength(dist_j[i]) == MAXN &&
                        Zlength(dist_j[k]) == MAXN &&
                        dkj == dist_j[k][j] &&
                        dik == dist_j[i][k] &&
                        dij == dist_j[i][j] &&
                        (forall (r: Z) (c: Z),
                          (0 <= r && r < MAXN &&
                           0 <= c && c < MAXN) =>
                            (0 <= dist_j[r][c] &&
                             dist_j[r][c] <= INF)) &&
                        safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                        FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                        FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                        FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                        GraphMatrixPtr::graph_rep(
                          MAXN,
                          FloydAdjacencyMatrix2Darray::matrix_rows_model,
                          dist, dist_j) *
                        store(&row_k, int *, row_k_ptr) *
                        store(&row_i, int *, row_i_ptr)
                */

                if (dik < INF && dkj < INF && dik + dkj < dij) {
                    row_i = graph_matrix_ptr_row(dist, i);
                    /*@ Assert
                          exists (dist_j: list (list Z)) (row_k_ptr : Z) (row_i_ptr : Z),
                            n == n@pre && dist == dist@pre &&
                            FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
                            0 <= n && n <= MAXN &&
                            0 <= k && k < n &&
                            0 <= k && k < MAXN &&
                            0 <= i && i < n &&
                            0 <= i && i < MAXN &&
                            0 <= j && j < n &&
                            0 <= j && j < MAXN &&
                            Zlength(dist_j[i]) == MAXN &&
                            Zlength(dist_j[k]) == MAXN &&
                            dkj == dist_j[k][j] &&
                            dik == dist_j[i][k] &&
                            dij == dist_j[i][j] &&
                            dik < INF && dkj < INF &&
                            dik + dkj < dij &&
                            (forall (r: Z) (c: Z),
                              (0 <= r && r < MAXN &&
                               0 <= c && c < MAXN) =>
                                (0 <= dist_j[r][c] &&
                                 dist_j[r][c] <= INF)) &&
                            safeExec(FloydAdjacencyMatrix2Darray::state_model(dist_j),
                            FloydAdjacencyMatrix2Darray::floyd_j_i_k_from(g, n, k, i, j), X) &&
                            FloydAdjacencyMatrix2Darray::matrix_shape(dist_j) &&
                            FloydAdjacencyMatrix2Darray::matrix_values_safe(dist_j) &&
                            GraphMatrixPtr::row_rep(
                              MAXN,
                              FloydAdjacencyMatrix2Darray::matrix_rows_model,
                              dist, i, row_i_ptr, dist_j) *
                            store(&row_k, int *, row_k_ptr) *
                            store(&row_i, int *, row_i_ptr)
                    */
                    row_i[j] = dik + dkj;
                }
            }
        }
    }
}
