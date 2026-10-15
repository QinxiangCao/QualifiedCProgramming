// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"
#include "array2_ext_def.h"
// #include <limits.h>
static int n, m, k, N, S, T, L, letters[26], ds[2500], dt[2500], q[2500], front[2500], nextf[2500],
    seen[2500], stamp, best = INT_MAX;
static char g[2501], beststr[2501];
static int allowed(int v, unsigned mask)
{
    char c = g[v];
    return c == 'S' || c == 'T' || (mask & (1u << (c - 'a')));
}
static void bfs(int src, unsigned mask, int *d)
{
    for (int i = 0; i < N; i++)
        d[i] = -1;
    int h = 0, t = 0;
    q[t++] = src;
    d[src] = 0;
    while (h < t)
    {
        int v = q[h++], r = v / m, c = v % m, u;
        int nb[4] = {v - m, v + m, v - 1, v + 1};
        for (int z = 0; z < 4; z++)
        {
            u = nb[z];
            if ((z == 0 && r == 0) || (z == 1 && r + 1 == n) || (z == 2 && c == 0) ||
                (z == 3 && c + 1 == m))
                continue;
            if (d[u] < 0 && allowed(u, mask))
            {
                d[u] = d[v] + 1;
                q[t++] = u;
            }
        }
    }
}
static void evaluate(unsigned mask)
{
    bfs(S, mask, ds);
    if (ds[T] < 0 || ds[T] > best)
        return;
    bfs(T, mask, dt);
    int D = ds[T], fs = 1;
    front[0] = S;
    char out[2501];
    int olen = 0;
    for (int step = 1; step <= D; step++)
    {
        char mn = '{';
        int ns = 0;
        ++stamp;
        for (int i = 0; i < fs; i++)
        {
            int v = front[i], r = v / m, c = v % m;
            int nb[4] = {v - m, v + m, v - 1, v + 1};
            for (int z = 0; z < 4; z++)
            {
                int u = nb[z];
                if ((z == 0 && r == 0) || (z == 1 && r + 1 == n) || (z == 2 && c == 0) ||
                    (z == 3 && c + 1 == m))
                    continue;
                if (ds[u] != step || dt[u] != D - step)
                    continue;
                if (step == D)
                {
                    if (u == T && seen[u] != stamp)
                    {
                        seen[u] = stamp;
                        nextf[ns++] = u;
                    }
                }
                else if (g[u] >= 'a' && g[u] <= 'z')
                {
                    if (g[u] < mn)
                    {
                        mn = g[u];
                        ns = 0;
                        ++stamp;
                    }
                    if (g[u] == mn && seen[u] != stamp)
                    {
                        seen[u] = stamp;
                        nextf[ns++] = u;
                    }
                }
            }
        }
        if (step < D)
            out[olen++] = mn;
        memcpy(front, nextf, (size_t)ns * sizeof(int));
        fs = ns;
    }
    out[olen] = '\0';
    if (D < best || (D == best && strcmp(out, beststr) < 0))
    {
        best = D;
        strcpy(beststr, out);
    }
}
static void gen(int at, int need, unsigned mask)
{
    if (!need)
    {
        evaluate(mask);
        return;
    }
    for (int i = at; i <= L - need; i++)
        gen(i + 1, need - 1, mask | (1u << letters[i]));
}
/* QCP_INSERT_BEGIN:P086_83C_track.support */
/*@ Extern Coq
      (Pre : Z -> list (list Z) -> Prop)
      (Spec : Z -> list (list Z) -> option (list Z) -> Prop)
      (IntArray::full_shape : Z -> Z -> Assertion)
      (CharArray::full_shape : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P086_83C_track_lib */
/* QCP_INSERT_END:P086_83C_track.support */
static int solver(int rows, int cols, int allowed_count, const char *grid,
                  char *out) /* QCP_INSERT_BEGIN:P086_83C_track.contract */

/*@ With (k : Z)
             (grid_data : list (list Z))
    Require
      1 <= Zlength(grid_data) && Zlength(grid_data) <= 50 &&
      1 <= k && k <= 4 &&
      rows == Zlength(grid_data) && allowed_count == k &&
      1 <= cols && cols <= 50 &&
      (forall i, (0 <= i && i < rows) => Zlength(grid_data[i]) == cols) &&
      (forall i j, (0 <= i && i < rows && 0 <= j && j < cols) =>
        ((Znth(j, Znth(i, grid_data, nil), 0) == 83) ||
         (Znth(j, Znth(i, grid_data, nil), 0) == 84) ||
         (97 <= Znth(j, Znth(i, grid_data, nil), 0) &&
          Znth(j, Znth(i, grid_data, nil), 0) <= 122))) &&
      Pre(k, grid_data) &&
      CharArray2::full(grid, rows, cols, grid_data) *
      IntArray::full_shape(letters, 26) *
      IntArray::full_shape(ds, rows * cols) *
      IntArray::full_shape(dt, rows * cols) *
      IntArray::full_shape(q, rows * cols) *
      IntArray::full_shape(front, rows * cols) *
      IntArray::full_shape(nextf, rows * cols) *
      IntArray::full_shape(seen, rows * cols) *
      CharArray::full_shape(g, rows * cols) *
      CharArray::full_shape(beststr, rows * cols + 1) *
      CharArray::undef_full(out, rows * cols + 1)
    Ensure
      CharArray2::full(grid, rows, cols, grid_data) *
      IntArray::full_shape(letters, 26) *
      IntArray::full_shape(ds, rows * cols) *
      IntArray::full_shape(dt, rows * cols) *
      IntArray::full_shape(q, rows * cols) *
      IntArray::full_shape(front, rows * cols) *
      IntArray::full_shape(nextf, rows * cols) *
      IntArray::full_shape(seen, rows * cols) *
      CharArray::full_shape(g, rows * cols) *
      CharArray::full_shape(beststr, rows * cols + 1) *
      ((__return == 0 && Spec(k, grid_data, None) &&
        CharArray::undef_full(out, rows * cols + 1)) ||
       (exists result,
          __return == 1 && Spec(k, grid_data, Some(result)) &&
          CharArray::full(out, Zlength(result) + 1, app(result, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(result) + 1, rows * cols + 1)))
*/
/* QCP_INSERT_END:P086_83C_track.contract */
{
    n = rows;
    m = cols;
    k = allowed_count;
    N = n * m;
    L = 0;
    stamp = 0;
    best = INT_MAX;
    beststr[0] = '\0';
    for (int i = 0; i < N; i++)
        seen[i] = 0;
    int present[26] = {0};
    for (int v = 0; v < N; ++v)
    {
        g[v] = grid[v];
        if (g[v] == 'S')
            S = v;
        else if (g[v] == 'T')
            T = v;
        else
            present[g[v] - 'a'] = 1;
    }
    for (int c = 0; c < 26; c++)
        if (present[c])
            letters[L++] = c;
    int take = k < L ? k : L;
    gen(0, take, 0);
    if (best == INT_MAX)
        return 0;
    strcpy(out, beststr);
    return 1;
}
// int main(void)
// {
//     int rows, cols, allowed_count;
//     if (scanf("%d%d%d", &rows, &cols, &allowed_count) != 3)
//         return 0;
//     char *grid = malloc((size_t)rows * cols);
//     for (int i = 0; i < rows; i++)
//     {
//         char row[55];
//         scanf("%s", row);
//         memcpy(grid + (size_t)i * cols, row, (size_t)cols);
//     }
//     char *out = malloc((size_t)rows * cols + 1);
//     if (solver(rows, cols, allowed_count, grid, out))
//         puts(out);
//     else
//         puts("-1");
//     free(grid);
//     free(out);
//     return 0;
// }
