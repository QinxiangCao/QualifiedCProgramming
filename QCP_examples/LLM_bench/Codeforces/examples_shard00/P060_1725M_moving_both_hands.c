/* Codeforces 1725/M - Moving Both Hands */
// #include <stdio.h>
// #include <stdlib.h>
// #include <limits.h>
typedef struct
{
    int to, next;
    long long w;
} Edge;
typedef struct
{
    long long d;
    int v;
} HeapNode;
static void push(HeapNode *h, int *sz, HeapNode x)
{
    int i = ++*sz;
    while (i > 1 && h[i / 2].d > x.d)
    {
        h[i] = h[i / 2];
        i /= 2;
    }
    h[i] = x;
}
static HeapNode pop(HeapNode *h, int *sz)
{
    HeapNode r = h[1], x = h[(*sz)--];
    int i = 1;
    while (i * 2 <= *sz)
    {
        int c = i * 2;
        if (c + 1 <= *sz && h[c + 1].d < h[c].d)
            ++c;
        if (h[c].d >= x.d)
            break;
        h[i] = h[c];
        i = c;
    }
    h[i] = x;
    return r;
}
#define ADD(u, v, z)                                                                               \
    do                                                                                             \
    {                                                                                              \
        e[ec] = (Edge){v, head[u], z};                                                             \
        head[u] = ec++;                                                                            \
    } while (0)
/* QCP_INSERT_BEGIN:P060_1725M_moving_both_hands.support */
/*@ Extern Coq
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (Spec : Z -> list (Z * Z * Z) -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P060_1725M_moving_both_hands_lib */
/* QCP_INSERT_END:P060_1725M_moving_both_hands.support */
static void solver(int n, int m, const int *eu, const int *ev, const long long *ew,
                   long long *out) /* QCP_INSERT_BEGIN:P060_1725M_moving_both_hands.contract */

/*@ With (edges : list (Z * Z * Z))
             (froms tos weights : list Z)
    Require
      2 <= n && n <= 100000 &&
      Zlength(edges) <= 200000 &&
      m == Zlength(edges) &&
      Zlength(froms) == m && Zlength(tos) == m && Zlength(weights) == m &&
      (forall i, (0 <= i && i < m) =>
        (ztriple_1(edges[i]) == froms[i] + 1 &&
         ztriple_2(edges[i]) == tos[i] + 1 &&
         ztriple_3(edges[i]) == weights[i])) &&
      IntArray::full(eu, m, froms) *
      IntArray::full(ev, m, tos) *
      Int64Array::full(ew, m, weights) *
      Int64Array::undef_full(out, n - 1)
    Ensure
      exists result,
        Spec(n, edges, result) &&
        IntArray::full(eu, m, froms) *
        IntArray::full(ev, m, tos) *
        Int64Array::full(ew, m, weights) *
        Int64Array::full(out, n - 1, result)
*/
/* QCP_INSERT_END:P060_1725M_moving_both_hands.contract */
{
    int N = 2 * n, *head = malloc((size_t)N * sizeof(*head));
    for (int i = 0; i < N; ++i)
        head[i] = -1;
    Edge *e = malloc((size_t)(2 * m + n) * sizeof(*e));
    int ec = 0;
    for (int i = 0; i < m; ++i)
    {
        int u = eu[i], v = ev[i];
        long long w = ew[i];
        ADD(u, v, w);
        ADD(v + n, u + n, w);
    }
    for (int i = 0; i < n; ++i)
        ADD(i, i + n, 0);
    long long *dist = malloc((size_t)N * sizeof(*dist));
    for (int i = 0; i < N; ++i)
        dist[i] = LLONG_MAX / 4;
    HeapNode *h = malloc((size_t)(4 * m + 4 * n + 10) * sizeof(*h));
    int hs = 0;
    dist[0] = 0;
    push(h, &hs, (HeapNode){0, 0});
    while (hs)
    {
        HeapNode cur = pop(h, &hs);
        if (cur.d != dist[cur.v])
            continue;
        for (int z = head[cur.v]; z != -1; z = e[z].next)
        {
            long long nd = cur.d + e[z].w;
            if (nd < dist[e[z].to])
            {
                dist[e[z].to] = nd;
                push(h, &hs, (HeapNode){nd, e[z].to});
            }
        }
    }
    for (int i = 1; i < n; ++i)
        out[i - 1] = dist[i + n] >= LLONG_MAX / 8 ? -1 : dist[i + n];
    free(head);
    free(e);
    free(dist);
    free(h);
}
// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     int *eu = malloc((size_t)m * sizeof(*eu)), *ev = malloc((size_t)m * sizeof(*ev));
//     long long *ew = malloc((size_t)m * sizeof(*ew)), *out = malloc((size_t)(n - 1) * sizeof(*out));
//     for (int i = 0; i < m; ++i)
//     {
//         scanf("%d %d %lld", &eu[i], &ev[i], &ew[i]);
//         --eu[i];
//         --ev[i];
//     }
//     solver(n, m, eu, ev, ew, out);
//     for (int i = 0; i + 1 < n; ++i)
//         printf("%lld%c", out[i], i + 2 == n ? '\n' : ' ');
//     free(eu);
//     free(ev);
//     free(ew);
//     free(out);
//     return 0;
// }
