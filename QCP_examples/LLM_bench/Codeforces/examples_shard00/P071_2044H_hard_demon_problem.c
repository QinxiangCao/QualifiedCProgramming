/* Codeforces 2044/H - Hard Demon Problem */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;

/* QCP needs explicit allocator contracts because the standard-library header is
 * intentionally unavailable to the symbolic-execution front end. */
void *calloc(size_t nmemb, size_t size)
/*@ calloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, cap, repeat_Z(0, cap))
*/;

void free(void *ptr)
/*@ free_int64
    Require exists values cap,
      Int64Array::full(ptr, cap, values)
    Ensure emp
*/;

/* QCP_INSERT_BEGIN:P071_2044H_hard_demon_problem.support */
/*@ Extern Coq
      (Z::pow : Z -> Z -> Z)
      (zquad_1 : Z * Z * Z * Z -> Z)
      (zquad_2 : Z * Z * Z * Z -> Z)
      (zquad_3 : Z * Z * Z * Z -> Z)
      (zquad_4 : Z * Z * Z * Z -> Z)
      (RectLookup : list Z -> Z -> Z -> Z -> Z -> Z -> Z)
      (RectanglesBounded : list Z -> Z -> Z -> Prop)
      (RectIntermediatesSafe : list Z -> Z -> Prop)
      (MatrixValuesBounded : list Z -> Z -> Prop)
      (QueriesBounded : list (Z * Z * Z * Z) -> Z -> Prop)
      (RawQueriesEncode : list (Z * Z * Z * Z) -> list Z -> Prop)
      (PrefixTables : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (TablesReady : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (QueryArithmeticSafe : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OutputPrefix : list Z -> Z -> list (Z * Z * Z * Z) -> list Z -> Z -> Prop)
      (Spec : list Z -> Z -> list (Z * Z * Z * Z) -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P071_2044H_hard_demon_problem_lib */
/* QCP_INSERT_END:P071_2044H_hard_demon_problem.support */

static long long rect(const long long *p, int stride, int x1, int y1, int x2, int y2)
/*@ rect_spec
    With (values : list Z) (bound : Z)
    Require
      2 <= stride && stride <= 2001 &&
      1 <= x1 && x1 <= x2 && x2 < stride &&
      1 <= y1 && y1 <= y2 && y2 < stride &&
      0 <= bound && bound <= 4002000000000000 &&
      Zlength(values) == stride * stride &&
      RectanglesBounded(values, stride, bound) &&
      RectIntermediatesSafe(values, stride) &&
      Int64Array::full(p, stride * stride, values)
    Ensure
      __return == RectLookup(values, stride, x1, y1, x2, y2) &&
      0 <= __return && __return <= bound &&
      Int64Array::full(p, stride * stride, values)
*/
{
    /*@ 0 <= x2 * stride + y2 && x2 * stride + y2 < stride * stride &&
        0 <= (x1 - 1) * stride + y2 &&
          (x1 - 1) * stride + y2 < stride * stride &&
        0 <= x2 * stride + y1 - 1 &&
          x2 * stride + y1 - 1 < stride * stride &&
        0 <= (x1 - 1) * stride + y1 - 1 &&
          (x1 - 1) * stride + y1 - 1 < stride * stride by local */
    return p[x2 * stride + y2] - p[(x1 - 1) * stride + y2] - p[x2 * stride + y1 - 1] +
           p[(x1 - 1) * stride + y1 - 1];
}
static void solver(int n, const long long *matrix, int q, const int *queries,
                   long long *out) /* QCP_INSERT_BEGIN:P071_2044H_hard_demon_problem.contract */

/*@ With (matrix_data : list Z)
             (queries_data : list (Z * Z * Z * Z))
             (raw_queries : list Z)
    Require
      1 <= n && n <= 2000 &&
      Zlength(matrix_data) == n * n &&
      MatrixValuesBounded(matrix_data, n) &&
      1 <= Zlength(queries_data) && Zlength(queries_data) <= 1000000 &&
      QueriesBounded(queries_data, n) &&
      (forall i, (0 <= i && i < Zlength(queries_data)) =>
        ((0 <= zquad_1(queries_data[i]) &&
          zquad_1(queries_data[i]) <= zquad_3(queries_data[i])) &&
         zquad_3(queries_data[i]) < n &&
         (0 <= zquad_2(queries_data[i]) &&
          zquad_2(queries_data[i]) <= zquad_4(queries_data[i])) &&
         zquad_4(queries_data[i]) < n)) &&
      q == Zlength(queries_data) &&
      RawQueriesEncode(queries_data, raw_queries) &&
      Int64Array::full(matrix, n * n, matrix_data) *
      IntArray::full(queries, 4 * q, raw_queries) *
      Int64Array::undef_full(out, q)
    Ensure
      exists result,
        Spec(matrix_data, n, queries_data, result) &&
        Int64Array::full(matrix, n * n, matrix_data) *
        IntArray::full(queries, 4 * q, raw_queries) *
        Int64Array::full(out, q, result)
*/
/* QCP_INSERT_END:P071_2044H_hard_demon_problem.contract */
{
    int S = n + 1;
    size_t cells = (size_t)S * S;
    long long *sum = calloc(cells, sizeof(*sum))
        /*@ where (calloc_int64) cap = cells */;
    long long *row = calloc(cells, sizeof(*row))
        /*@ where (calloc_int64) cap = cells */;
    long long *col = calloc(cells, sizeof(*col))
        /*@ where (calloc_int64) cap = cells */;
    /*@ Inv Assert
        exists sum_l row_l col_l,
          n == n@pre && matrix == matrix@pre && q == q@pre &&
          queries == queries@pre && out == out@pre &&
          S == n@pre + 1 && cells == S * S &&
          1 <= n@pre && n@pre <= 2000 && 1 <= q@pre && q@pre <= 1000000 &&
          Zlength(matrix_data) == n@pre * n@pre &&
          Zlength(queries_data) == q@pre &&
          MatrixValuesBounded(matrix_data, n@pre) &&
          QueriesBounded(queries_data, n@pre) &&
          RawQueriesEncode(queries_data, raw_queries) &&
          1 <= i && i <= n@pre + 1 &&
          PrefixTables(matrix_data, sum_l, row_l, col_l,
            n@pre, S, i * S) &&
          Int64Array::full(matrix@pre, n@pre * n@pre, matrix_data) *
          IntArray::full(queries@pre, 4 * q@pre, raw_queries) *
          Int64Array::undef_full(out@pre, q@pre) *
          Int64Array::full(sum, S * S, sum_l) *
          Int64Array::full(row, S * S, row_l) *
          Int64Array::full(col, S * S, col_l)
    */
    for (int i = 1; i <= n; ++i)
        /*@ Inv Assert
            exists sum_l row_l col_l,
              n == n@pre && matrix == matrix@pre && q == q@pre &&
              queries == queries@pre && out == out@pre &&
              S == n@pre + 1 && cells == S * S &&
              1 <= n@pre && n@pre <= 2000 && 1 <= q@pre && q@pre <= 1000000 &&
              Zlength(matrix_data) == n@pre * n@pre &&
              Zlength(queries_data) == q@pre &&
              MatrixValuesBounded(matrix_data, n@pre) &&
              QueriesBounded(queries_data, n@pre) &&
              RawQueriesEncode(queries_data, raw_queries) &&
              1 <= i && i <= n@pre && 1 <= j && j <= n@pre + 1 &&
              PrefixTables(matrix_data, sum_l, row_l, col_l,
                n@pre, S, i * S + j) &&
              Int64Array::full(matrix@pre, n@pre * n@pre, matrix_data) *
              IntArray::full(queries@pre, 4 * q@pre, raw_queries) *
              Int64Array::undef_full(out@pre, q@pre) *
              Int64Array::full(sum, S * S, sum_l) *
              Int64Array::full(row, S * S, row_l) *
              Int64Array::full(col, S * S, col_l)
        */
        for (int j = 1; j <= n; ++j)
        {
            /*@ 0 <= (i - 1) * n + j - 1 &&
                (i - 1) * n + j - 1 < n * n by local */
            long long x = matrix[(i - 1) * n + j - 1];
            size_t z = (size_t)i * S + j;
            /*@ 0 <= z - S - 1 && z - S - 1 < cells &&
                0 <= z - S && z - S < cells &&
                0 <= z - 1 && z - 1 < cells &&
                0 <= z && z < cells by local */
            sum[z] = x + sum[z - S] + sum[z - 1] - sum[z - S - 1];
            row[z] = x * i + row[z - S] + row[z - 1] - row[z - S - 1];
            col[z] = x * j + col[z - S] + col[z - 1] - col[z - S - 1];
        }
    /*@ Assert
        exists sum_l row_l col_l,
          n == n@pre && matrix == matrix@pre && q == q@pre &&
          queries == queries@pre && out == out@pre &&
          S == n@pre + 1 && cells == S * S &&
          1 <= n@pre && n@pre <= 2000 && 1 <= q@pre && q@pre <= 1000000 &&
          Zlength(matrix_data) == n@pre * n@pre &&
          Zlength(queries_data) == q@pre &&
          MatrixValuesBounded(matrix_data, n@pre) &&
          QueriesBounded(queries_data, n@pre) &&
          RawQueriesEncode(queries_data, raw_queries) &&
          TablesReady(matrix_data, sum_l, row_l, col_l, n@pre, S) &&
          Int64Array::full(matrix@pre, n@pre * n@pre, matrix_data) *
          IntArray::full(queries@pre, 4 * q@pre, raw_queries) *
          Int64Array::undef_full(out@pre, q@pre) *
          Int64Array::full(sum, S * S, sum_l) *
          Int64Array::full(row, S * S, row_l) *
          Int64Array::full(col, S * S, col_l)
    */
    /*@ Inv Assert
        exists sum_l row_l col_l result,
          n == n@pre && matrix == matrix@pre && q == q@pre &&
          queries == queries@pre && out == out@pre &&
          S == n@pre + 1 && cells == S * S &&
          1 <= n@pre && n@pre <= 2000 && 1 <= q@pre && q@pre <= 1000000 &&
          Zlength(matrix_data) == n@pre * n@pre &&
          Zlength(queries_data) == q@pre &&
          MatrixValuesBounded(matrix_data, n@pre) &&
          QueriesBounded(queries_data, n@pre) &&
          RawQueriesEncode(queries_data, raw_queries) &&
          0 <= i && i <= q@pre &&
          TablesReady(matrix_data, sum_l, row_l, col_l, n@pre, S) &&
          OutputPrefix(matrix_data, n@pre, queries_data, result, i) &&
          Int64Array::full(matrix@pre, n@pre * n@pre, matrix_data) *
          IntArray::full(queries@pre, 4 * q@pre, raw_queries) *
          Int64Array::seg(out@pre, 0, i, result) *
          Int64Array::undef_seg(out@pre, i, q@pre) *
          Int64Array::full(sum, S * S, sum_l) *
          Int64Array::full(row, S * S, row_l) *
          Int64Array::full(col, S * S, col_l)
    */
    for (int i = 0; i < q; ++i)
    {
        int x1 = queries[4 * i], y1 = queries[4 * i + 1], x2 = queries[4 * i + 2],
            y2 = queries[4 * i + 3];
        /*@ Assert
            exists sum_l row_l col_l result,
              n == n@pre && matrix == matrix@pre && q == q@pre &&
              queries == queries@pre && out == out@pre &&
              S == n@pre + 1 && cells == S * S &&
              1 <= n@pre && n@pre <= 2000 && 1 <= q@pre && q@pre <= 1000000 &&
              Zlength(matrix_data) == n@pre * n@pre &&
              Zlength(queries_data) == q@pre &&
              MatrixValuesBounded(matrix_data, n@pre) &&
              QueriesBounded(queries_data, n@pre) &&
              RawQueriesEncode(queries_data, raw_queries) &&
              0 <= i && i < q@pre &&
              x1 == zquad_1(queries_data[i]) + 1 &&
              y1 == zquad_2(queries_data[i]) + 1 &&
              x2 == zquad_3(queries_data[i]) + 1 &&
              y2 == zquad_4(queries_data[i]) + 1 &&
              1 <= x1 && x1 <= x2 && x2 < S &&
              1 <= y1 && y1 <= y2 && y2 < S &&
              TablesReady(matrix_data, sum_l, row_l, col_l, n@pre, S) &&
              RectanglesBounded(sum_l, S, 4 * Z::pow(10, 12)) &&
              RectanglesBounded(row_l, S, 4002000000000000) &&
              RectanglesBounded(col_l, S, 4002000000000000) &&
              RectIntermediatesSafe(sum_l, S) &&
              RectIntermediatesSafe(row_l, S) &&
              RectIntermediatesSafe(col_l, S) &&
              QueryArithmeticSafe(sum_l, row_l, col_l, S, x1, y1, x2, y2) &&
              OutputPrefix(matrix_data, n@pre, queries_data, result, i) &&
              Int64Array::full(matrix@pre, n@pre * n@pre, matrix_data) *
              IntArray::full(queries@pre, 4 * q@pre, raw_queries) *
              Int64Array::seg(out@pre, 0, i, result) *
              Int64Array::undef_seg(out@pre, i, q@pre) *
              Int64Array::full(sum, S * S, sum_l) *
              Int64Array::full(row, S * S, row_l) *
              Int64Array::full(col, S * S, col_l)
        */
        long long sm = rect(sum, S, x1, y1, x2, y2)
                      /*@ where (rect_spec) bound = 4 * Z::pow(10, 12) */,
                  rs = rect(row, S, x1, y1, x2, y2)
                      /*@ where (rect_spec) bound = 4002000000000000 */,
                  cs = rect(col, S, x1, y1, x2, y2)
                      /*@ where (rect_spec) bound = 4002000000000000 */,
                  w = y2 - y1 + 1;
        out[i] = w * (rs - (long long)x1 * sm) + cs - (long long)(y1 - 1) * sm;
    }
    free(sum);
    free(row);
    free(col);
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n, q;
//         scanf("%d %d", &n, &q);
//         long long *matrix = malloc((size_t)n * n * sizeof(*matrix)),
//                   *out = malloc((size_t)q * sizeof(*out));
//         int *queries = malloc((size_t)4 * q * sizeof(*queries));
//         for (int i = 0; i < n * n; ++i)
//             scanf("%lld", &matrix[i]);
//         for (int i = 0; i < 4 * q; ++i)
//             scanf("%d", &queries[i]);
//         solver(n, matrix, q, queries, out);
//         for (int i = 0; i < q; ++i)
//             printf("%lld%c", out[i], i + 1 == q ? '\n' : ' ');
//         free(matrix);
//         free(queries);
//         free(out);
//     }
//     return 0;
// }
