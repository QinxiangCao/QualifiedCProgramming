// #include <stdio.h>
// #include <stdlib.h>
#include "array2_ext_def.h"

#define LOG 20
typedef long long i64;
typedef struct
{
    int to, next;
} Edge;

static int *head, *par, *dep, *sz, (*up)[LOG], *order;
static Edge *edges;
static int ec;
static void add_edge(int u, int v)
{
    edges[ec] = (Edge){v, head[u]};
    head[u] = ec++;
}
static int lca(int a, int b)
{
    if (dep[a] < dep[b])
    {
        int t = a;
        a = b;
        b = t;
    }
    int d = dep[a] - dep[b];
    for (int j = 0; j < LOG; j++)
        if ((d >> j) & 1)
            a = up[a][j];
    if (a == b)
        return a;
    for (int j = LOG - 1; j >= 0; j--)
        if (up[a][j] != up[b][j])
            a = up[a][j], b = up[b][j];
    return par[a];
}
static int distv(int a, int b)
{
    int c = lca(a, b);
    return dep[a] + dep[b] - 2 * dep[c];
}
static int on_path(int x, int a, int b)
{
    return distv(a, x) + distv(x, b) == distv(a, b);
}
static int jump_up(int v, int d)
{
    for (int j = 0; j < LOG; j++)
        if ((d >> j) & 1)
            v = up[v][j];
    return v;
}
static i64 side_size(int u, int v, int n)
{
    if (lca(u, v) == u)
    {
        int ch = jump_up(v, dep[v] - dep[u] - 1);
        return n - sz[ch];
    }
    return sz[u];
}
/* QCP_INSERT_BEGIN:P084_1527D_mex_tree.support */
/*@ Extern Coq
      (Pre : Z -> list (Z * Z) -> Prop)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> list (Z * Z) -> list Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P084_1527D_mex_tree_lib */
/* QCP_INSERT_END:P084_1527D_mex_tree.support */
static void solver(int n, const int *eu, const int *ev,
                   i64 *ans) /* QCP_INSERT_BEGIN:P084_1527D_mex_tree.contract */

/*@ With (edges : list (Z * Z))
             (froms tos : list Z)
    Require
      2 <= n && n <= 200000 &&
      Zlength(edges) == n-1 &&
      (forall i, (0 <= i && i < Zlength(edges)) => ((0 <= fst(edges[i]) && fst(edges[i]) < n) && (0 <= snd(edges[i]) && snd(edges[i]) < n))) &&
      Pre(n, edges) &&
      Zlength(froms) == n - 1 && Zlength(tos) == n - 1 &&
      (forall i, (0 <= i && i < n - 1) =>
        (fst(edges[i]) == froms[i] &&
         snd(edges[i]) == tos[i])) &&
      IntArray::full(eu, n - 1, froms) *
      IntArray::full(ev, n - 1, tos) *
      Int64Array::undef_full(ans, n + 1)
    Ensure
      exists out,
        Spec(n, edges, out) &&
        IntArray::full(eu, n - 1, froms) *
        IntArray::full(ev, n - 1, tos) *
        Int64Array::full(ans, n + 1, out)
*/
/* QCP_INSERT_END:P084_1527D_mex_tree.contract */
{
    head = malloc((size_t)n * sizeof *head);
    par = malloc((size_t)n * sizeof *par);
    dep = malloc((size_t)n * sizeof *dep);
    sz = malloc((size_t)n * sizeof *sz);
    up = malloc((size_t)n * sizeof *up);
    order = malloc((size_t)n * sizeof *order);
    edges = malloc((size_t)(2 * n) * sizeof *edges);
    ec = 0;
    for (int i = 0; i < n; i++)
        head[i] = -1;
    for (int i = 0; i < n - 1; i++)
    {
        add_edge(eu[i], ev[i]);
        add_edge(ev[i], eu[i]);
    }
    int top = 0;
    order[top++] = 0;
    par[0] = 0;
    dep[0] = 0;
    for (int i = 0; i < top; i++)
    {
        int v = order[i];
        for (int e = head[v]; e != -1; e = edges[e].next)
        {
            int u = edges[e].to;
            if (u == par[v])
                continue;
            par[u] = v;
            dep[u] = dep[v] + 1;
            order[top++] = u;
        }
    }
    for (int i = 0; i < n; i++)
    {
        up[i][0] = par[i];
        for (int j = 1; j < LOG; j++)
            up[i][j] = up[up[i][j - 1]][j - 1];
        sz[i] = 1;
    }
    for (int i = n - 1; i > 0; i--)
        sz[par[order[i]]] += sz[order[i]];
    for (int i = 0; i <= n; i++)
        ans[i] = 0;
    i64 total = (i64)n * (n - 1) / 2, p1 = total;
    for (int e = head[0]; e != -1; e = edges[e].next)
    {
        i64 s = sz[edges[e].to];
        p1 -= s * (s - 1) / 2;
    }
    ans[0] = total - p1;
    i64 prev = p1;
    int a = 0, b = 0, ok = 1;
    for (int x = 1; x < n; x++)
    {
        if (ok)
        {
            if (on_path(x, a, b))
            {
            }
            else if (on_path(a, x, b))
                a = x;
            else if (on_path(b, a, x))
                b = x;
            else
                ok = 0;
        }
        i64 now = 0;
        if (ok)
        {
            if (a == b)
                now = p1;
            else
                now = side_size(a, b, n) * side_size(b, a, n);
        }
        ans[x] = prev - now;
        prev = now;
    }
    ans[n] = prev;
    free(edges);
    free(order);
    free(up);
    free(sz);
    free(dep);
    free(par);
    free(head);
}
// int main(void)
// {
//     int T;
//     if (scanf("%d", &T) != 1)
//         return 0;
//     while (T--)
//     {
//         int n;
//         scanf("%d", &n);
//         int *eu = malloc((size_t)(n - 1) * sizeof *eu), *ev = malloc((size_t)(n - 1) * sizeof *ev);
//         i64 *ans = malloc((size_t)(n + 1) * sizeof *ans);
//         for (int i = 0; i < n - 1; i++)
//             scanf("%d%d", &eu[i], &ev[i]);
//         solver(n, eu, ev, ans);
//         for (int i = 0; i <= n; i++)
//             printf("%lld%c", ans[i], i == n ? '\n' : ' ');
//         free(eu);
//         free(ev);
//         free(ans);
//     }
//     return 0;
// }
