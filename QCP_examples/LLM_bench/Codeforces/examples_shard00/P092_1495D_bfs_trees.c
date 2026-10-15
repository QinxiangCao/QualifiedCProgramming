// #include <stdio.h>
// #include <stdlib.h>
#define MOD 998244353LL
typedef long long i64;
typedef struct
{
    int to, next;
} Edge;
/* QCP_INSERT_BEGIN:P092_1495D_bfs_trees.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : Z -> list (Z * Z) -> Prop)
      (Spec : Z -> list (Z * Z) -> list (list Z) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array2::full : Z -> Z -> Z -> list (list Z) -> Assertion)
      (Int64Array2::undef_full : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P092_1495D_bfs_trees_lib */
/* QCP_INSERT_END:P092_1495D_bfs_trees.support */
static void solver(int n, int m, const int *eu, const int *ev,
                   i64 *out) /* QCP_INSERT_BEGIN:P092_1495D_bfs_trees.contract */

/*@ With (edges : list (Z * Z))
             (froms tos : list Z)
    Require
      1 <= n && n <= 400 &&
      Zlength(edges) <= 600 &&
      Pre(n, edges) &&
      m == Zlength(edges) &&
      Zlength(froms) == m && Zlength(tos) == m &&
      (forall i, (0 <= i && i < m) =>
        (fst(edges[i]) == froms[i] + 1 &&
         snd(edges[i]) == tos[i] + 1)) &&
      IntArray::full(eu, m, froms) *
      IntArray::full(ev, m, tos) *
      Int64Array2::undef_full(out, n, n)
    Ensure
      exists result,
        Spec(n, edges, result) &&
        IntArray::full(eu, m, froms) *
        IntArray::full(ev, m, tos) *
        Int64Array2::full(out, n, n, result)
*/
/* QCP_INSERT_END:P092_1495D_bfs_trees.contract */
{
    int *head = malloc(n * sizeof *head);
    for (int i = 0; i < n; i++)
        head[i] = -1;
    Edge *ed = malloc((size_t)2 * m * sizeof *ed);
    int ec = 0;
    for (int i = 0; i < m; i++)
    {
        int u = eu[i], v = ev[i];
        ed[ec] = (Edge){v, head[u]};
        head[u] = ec++;
        ed[ec] = (Edge){u, head[v]};
        head[v] = ec++;
    }
    int *d = malloc((size_t)n * n * sizeof *d), *q = malloc(n * sizeof *q);
    for (int s = 0; s < n; s++)
    {
        int *ds = d + s * n;
        for (int i = 0; i < n; i++)
            ds[i] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        ds[s] = 0;
        while (h < t)
        {
            int v = q[h++];
            for (int e = head[v]; e != -1; e = ed[e].next)
            {
                int u = ed[e].to;
                if (ds[u] < 0)
                {
                    ds[u] = ds[v] + 1;
                    q[t++] = u;
                }
            }
        }
    }
    for (int x = 0; x < n; x++)
    {
        for (int y = 0; y < n; y++)
        {
            int D = d[x * n + y], on = 0;
            for (int v = 0; v < n; v++)
                if (d[x * n + v] + d[y * n + v] == D)
                    on++;
            i64 ans = on == D + 1 ? 1 : 0;
            if (ans)
                for (int v = 0; v < n; v++)
                    if (d[x * n + v] + d[y * n + v] != D)
                    {
                        int ways = 0;
                        for (int e = head[v]; e != -1; e = ed[e].next)
                        {
                            int u = ed[e].to;
                            if (d[x * n + u] + 1 == d[x * n + v] &&
                                d[y * n + u] + 1 == d[y * n + v])
                                ways++;
                        }
                        ans = ans * ways % MOD;
                    }
            out[x * n + y] = ans;
        }
    }
    free(q);
    free(d);
    free(ed);
    free(head);
}
// int main(void)
// {
//     int n, m;
//     if (scanf("%d%d", &n, &m) != 2)
//         return 0;
//     int *eu = malloc((size_t)m * sizeof *eu), *ev = malloc((size_t)m * sizeof *ev);
//     i64 *out = malloc((size_t)n * n * sizeof *out);
//     for (int i = 0; i < m; i++)
//     {
//         scanf("%d%d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     solver(n, m, eu, ev, out);
//     for (int x = 0; x < n; x++)
//         for (int y = 0; y < n; y++)
//             printf("%lld%c", out[x * n + y], y + 1 == n ? '\n' : ' ');
//     free(eu);
//     free(ev);
//     free(out);
//     return 0;
// }
