// #include <stdio.h>
// #include <stdlib.h>
#include "array2_ext_def.h"
#define LOG 19
typedef long long i64;
typedef struct
{
    int u, v, w, id, tree;
} E;
typedef struct
{
    int to, w, id, next;
} TE;
static int cmpe(const void *A, const void *B)
{
    const E *a = A, *b = B;
    return a->w == b->w ? a->id - b->id : a->w - b->w;
}
static int *dsu;
static int find(int x)
{
    int r = x;
    while (dsu[r] != r)
        r = dsu[r];
    while (dsu[x] != x)
    {
        int y = dsu[x];
        dsu[x] = r;
        x = y;
    }
    return r;
}
/* QCP_INSERT_BEGIN:P095_827D_best_edge_weight.support */
/*@ Extern Coq
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (Pre : Z -> list (Z * Z * Z) -> Prop)
      (Spec : Z -> list (Z * Z * Z) -> list Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P095_827D_best_edge_weight_lib */
/* QCP_INSERT_END:P095_827D_best_edge_weight.support */
static void solver(int n, int m, const E *input,
                   i64 *out) /* QCP_INSERT_BEGIN:P095_827D_best_edge_weight.contract */

/*@ With (edges : list (Z * Z * Z))
             (input_mem : list (option Z))
    Require
      2 <= n && n <= 200000 &&
      n-1 <= Zlength(edges) && Zlength(edges) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (1 <= ztriple_1(edges[i]) && ztriple_1(edges[i]) <= n &&
         1 <= ztriple_2(edges[i]) && ztriple_2(edges[i]) <= n)) &&
      Pre(n, edges) &&
      m == Zlength(edges) && Zlength(input_mem) == 5 * m &&
      (forall i, (0 <= i && i < m) =>
        (input_mem[5 * i] == Some(ztriple_1(edges[i]) - 1) &&
         input_mem[5 * i + 1] == Some(ztriple_2(edges[i]) - 1) &&
         input_mem[5 * i + 2] == Some(ztriple_3(edges[i])))) &&
      IntArray::mixed_full(input, 5 * m, input_mem) *
      Int64Array::undef_full(out, m)
    Ensure
      exists result,
        Spec(n, edges, result) &&
        IntArray::mixed_full(input, 5 * m, input_mem) *
        Int64Array::full(out, m, result)
*/
/* QCP_INSERT_END:P095_827D_best_edge_weight.contract */
{
    E *e = malloc(m * sizeof *e);
    for (int i = 0; i < m; i++)
    {
        e[i] = input[i];
        e[i].id = i;
        e[i].tree = 0;
    }
    E *sorted = malloc(m * sizeof *sorted);
    for (int i = 0; i < m; i++)
        sorted[i] = e[i];
    qsort(sorted, m, sizeof *sorted, cmpe);
    dsu = malloc(n * sizeof *dsu);
    for (int i = 0; i < n; i++)
        dsu[i] = i;
    int *head = malloc(n * sizeof *head);
    for (int i = 0; i < n; i++)
        head[i] = -1;
    TE *te = malloc((size_t)2 * (n - 1) * sizeof *te);
    int tc = 0;
    for (int i = 0; i < m; i++)
    {
        int a = find(sorted[i].u), b = find(sorted[i].v);
        if (a != b)
        {
            dsu[a] = b;
            sorted[i].tree = 1;
            e[sorted[i].id].tree = 1;
            int u = sorted[i].u, v = sorted[i].v, w = sorted[i].w, id = sorted[i].id;
            te[tc] = (TE){v, w, id, head[u]};
            head[u] = tc++;
            te[tc] = (TE){u, w, id, head[v]};
            head[v] = tc++;
        }
    }
    int(*up)[LOG] = malloc((size_t)n * sizeof *up), (*mx)[LOG] = malloc((size_t)n * sizeof *mx),
    *dep = malloc(n * sizeof *dep), *peid = malloc(n * sizeof *peid),
    *ord = malloc(n * sizeof *ord);
    int os = 1;
    ord[0] = 0;
    up[0][0] = 0;
    mx[0][0] = 0;
    dep[0] = 0;
    peid[0] = -1;
    for (int i = 0; i < os; i++)
    {
        int v = ord[i];
        for (int z = head[v]; z != -1; z = te[z].next)
        {
            int u = te[z].to;
            if (u == up[v][0])
                continue;
            up[u][0] = v;
            mx[u][0] = te[z].w;
            dep[u] = dep[v] + 1;
            peid[u] = te[z].id;
            ord[os++] = u;
        }
    }
    for (int j = 1; j < LOG; j++)
        for (int v = 0; v < n; v++)
        {
            up[v][j] = up[up[v][j - 1]][j - 1];
            int a = mx[v][j - 1], b = mx[up[v][j - 1]][j - 1];
            mx[v][j] = a > b ? a : b;
        }
    for (int i = 0; i < m; i++)
        out[i] = -1;
    for (int i = 0; i < m; i++)
        if (!e[i].tree)
        {
            int a = e[i].u, b = e[i].v, res = 0;
            if (dep[a] < dep[b])
            {
                int t = a;
                a = b;
                b = t;
            }
            int d = dep[a] - dep[b];
            for (int j = 0; j < LOG; j++)
                if ((d >> j) & 1)
                {
                    if (mx[a][j] > res)
                        res = mx[a][j];
                    a = up[a][j];
                }
            if (a != b)
            {
                for (int j = LOG - 1; j >= 0; j--)
                    if (up[a][j] != up[b][j])
                    {
                        if (mx[a][j] > res)
                            res = mx[a][j];
                        if (mx[b][j] > res)
                            res = mx[b][j];
                        a = up[a][j];
                        b = up[b][j];
                    }
                if (mx[a][0] > res)
                    res = mx[a][0];
                if (mx[b][0] > res)
                    res = mx[b][0];
            }
            out[i] = (i64)res - 1;
        }
    for (int i = 0; i < n; i++)
        dsu[i] = i;
    for (int z = 0; z < m; z++)
        if (!sorted[z].tree)
        {
            int a = sorted[z].u, b = sorted[z].v, x = a, y = b;
            if (dep[x] < dep[y])
            {
                int t = x;
                x = y;
                y = t;
            }
            int d = dep[x] - dep[y];
            for (int j = 0; j < LOG; j++)
                if ((d >> j) & 1)
                    x = up[x][j];
            if (x != y)
            {
                for (int j = LOG - 1; j >= 0; j--)
                    if (up[x][j] != up[y][j])
                    {
                        x = up[x][j];
                        y = up[y][j];
                    }
                x = up[x][0];
            }
            int c = x;
            a = find(a);
            while (dep[a] > dep[c])
            {
                out[peid[a]] = (i64)sorted[z].w - 1;
                dsu[a] = find(up[a][0]);
                a = find(a);
            }
            b = find(b);
            while (dep[b] > dep[c])
            {
                out[peid[b]] = (i64)sorted[z].w - 1;
                dsu[b] = find(up[b][0]);
                b = find(b);
            }
        }
    free(ord);
    free(peid);
    free(dep);
    free(mx);
    free(up);
    free(te);
    free(head);
    free(dsu);
    free(sorted);
    free(e);
    dsu = NULL;
}
// int main(void)
// {
//     int n, m;
//     if (scanf("%d%d", &n, &m) != 2)
//         return 0;
//     E *e = malloc(m * sizeof *e);
//     i64 *out = malloc(m * sizeof *out);
//     for (int i = 0; i < m; i++)
//     {
//         scanf("%d%d%d", &e[i].u, &e[i].v, &e[i].w);
//         --e[i].u;
//         --e[i].v;
//     }
//     solver(n, m, e, out);
//     for (int i = 0; i < m; i++)
//         printf("%lld%c", out[i], i + 1 == m ? '\n' : ' ');
//     free(out);
//     free(e);
//     return 0;
// }
