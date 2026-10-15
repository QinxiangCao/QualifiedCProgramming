// #include <stdio.h>
// #include <stdlib.h>
// #include <math.h>
typedef struct
{
    int to, next;
} Edge;
typedef struct
{
    int l, r, k, id, block;
} Query;
static int cmpq(const void *A, const void *B)
{
    const Query *a = A, *b = B;
    if (a->block != b->block)
        return a->block - b->block;
    return (a->block & 1) ? b->r - a->r : a->r - b->r;
}
static int *bit, n;
static void addbit(int x, int d)
{
    for (; x <= n; x += x & -x)
        bit[x] += d;
}
static int sum(int x)
{
    int s = 0;
    for (; x; x -= x & -x)
        s += bit[x];
    return s;
}
/* QCP_INSERT_BEGIN:P085_375D_tree_and_queries.support */
/*@ Extern Coq
      (Spec : list Z -> list (Z * Z) -> list (Z * Z) -> list Z -> Prop)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P085_375D_tree_and_queries_lib */
/* QCP_INSERT_END:P085_375D_tree_and_queries.support */
static void solver(int size, int m, const int *input_col, const int *eu, const int *ev,
                   const int *qv, const int *qk,
                   int *output) /* QCP_INSERT_BEGIN:P085_375D_tree_and_queries.contract */

/*@ With (colors : list Z)
             (edges : list (Z * Z))
             (queries : list (Z * Z))
             (eu_data ev_data qv_data qk_data : list Z)
    Require
      2 <= Zlength(colors) && Zlength(colors) <= 100000 &&
      Zlength(edges) == Zlength(colors)-1 &&
      1 <= Zlength(queries) && Zlength(queries) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(colors)) => (1 <= colors[i] && colors[i] <= 100000)) &&
      size == Zlength(colors) && m == Zlength(queries) &&
      Zlength(eu_data) == Zlength(edges) && Zlength(ev_data) == Zlength(edges) &&
      Zlength(qv_data) == Zlength(queries) && Zlength(qk_data) == Zlength(queries) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (eu_data[i] == fst(edges[i]) && ev_data[i] == snd(edges[i]))) &&
      (forall i, (0 <= i && i < Zlength(queries)) =>
        (qv_data[i] == fst(queries[i]) && qk_data[i] == snd(queries[i]))) &&
      IntArray::full(input_col, size, colors) *
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      IntArray::full(qv, m, qv_data) * IntArray::full(qk, m, qk_data) *
      IntArray::undef_full(output, m)
    Ensure
      exists result,
        Spec(colors, edges, queries, result) &&
        IntArray::full(input_col, size, colors) *
        IntArray::full(eu, Zlength(edges), eu_data) * IntArray::full(ev, Zlength(edges), ev_data) *
        IntArray::full(qv, m, qv_data) * IntArray::full(qk, m, qk_data) *
        IntArray::full(output, m, result)
*/
/* QCP_INSERT_END:P085_375D_tree_and_queries.contract */
{
    n = size;
    int *col = malloc(n * sizeof *col), *head = malloc(n * sizeof *head),
        *tin = malloc(n * sizeof *tin), *tout = malloc(n * sizeof *tout),
        *eul = malloc(n * sizeof *eul), *par = malloc(n * sizeof *par),
        *it = malloc(n * sizeof *it), *st = malloc(n * sizeof *st);
    for (int i = 0; i < n; i++)
        col[i] = input_col[i], head[i] = -1;
    Edge *ed = malloc(2 * (n - 1) * sizeof *ed);
    int ec = 0;
    for (int i = 0; i < n - 1; i++)
    {
        int u = eu[i], v = ev[i];
        ed[ec] = (Edge){v, head[u]};
        head[u] = ec++;
        ed[ec] = (Edge){u, head[v]};
        head[v] = ec++;
    }
    int timer = 0, sp = 0;
    st[sp++] = 0;
    par[0] = -1;
    it[0] = head[0];
    tin[0] = timer;
    eul[timer++] = 0;
    while (sp)
    {
        int v = st[sp - 1], e = it[v];
        while (e != -1 && ed[e].to == par[v])
            e = ed[e].next;
        it[v] = e;
        if (e == -1)
        {
            tout[v] = timer - 1;
            sp--;
            continue;
        }
        it[v] = ed[e].next;
        int u = ed[e].to;
        par[u] = v;
        tin[u] = timer;
        eul[timer++] = u;
        it[u] = head[u];
        st[sp++] = u;
    }
    int maxc = 0;
    for (int i = 0; i < n; i++)
        if (col[i] > maxc)
            maxc = col[i];
    int block = (int)sqrt((double)n) + 1;
    Query *q = malloc(m * sizeof *q);
    for (int i = 0; i < m; i++)
    {
        int v = qv[i], k = qk[i];
        q[i] = (Query){tin[v], tout[v], k, i, tin[v] / block};
    }
    qsort(q, m, sizeof *q, cmpq);
    int *freq = calloc((size_t)maxc + 1, sizeof *freq), *ans = malloc(m * sizeof *ans);
    bit = calloc((size_t)n + 1, sizeof *bit);
    int L = 0, R = -1;
    for (int z = 0; z < m; z++)
    {
        while (L > q[z].l)
        {
            int c = col[eul[--L]];
            if (freq[c])
                addbit(freq[c], -1);
            addbit(++freq[c], 1);
        }
        while (R < q[z].r)
        {
            int c = col[eul[++R]];
            if (freq[c])
                addbit(freq[c], -1);
            addbit(++freq[c], 1);
        }
        while (L < q[z].l)
        {
            int c = col[eul[L++]];
            addbit(freq[c], -1);
            if (--freq[c])
                addbit(freq[c], 1);
        }
        while (R > q[z].r)
        {
            int c = col[eul[R--]];
            addbit(freq[c], -1);
            if (--freq[c])
                addbit(freq[c], 1);
        }
        ans[q[z].id] = sum(n) - sum(q[z].k - 1);
    }
    for (int i = 0; i < m; i++)
        output[i] = ans[i];
    free(bit);
    free(ans);
    free(freq);
    free(q);
    free(st);
    free(it);
    free(par);
    free(eul);
    free(tout);
    free(tin);
    free(ed);
    free(head);
    free(col);
}
// int main(void)
// {
//     int size, m;
//     if (scanf("%d%d", &size, &m) != 2)
//         return 0;
//     int *col = malloc((size_t)size * sizeof *col), *eu = malloc((size_t)(size - 1) * sizeof *eu),
//         *ev = malloc((size_t)(size - 1) * sizeof *ev), *qv = malloc((size_t)m * sizeof *qv),
//         *qk = malloc((size_t)m * sizeof *qk), *out = malloc((size_t)m * sizeof *out);
//     for (int i = 0; i < size; i++)
//         scanf("%d", &col[i]);
//     for (int i = 0; i < size - 1; i++)
//     {
//         scanf("%d%d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     for (int i = 0; i < m; i++)
//     {
//         scanf("%d%d", &qv[i], &qk[i]);
//         --qv[i];
//     }
//     solver(size, m, col, eu, ev, qv, qk, out);
//     for (int i = 0; i < m; i++)
//         printf("%d\n", out[i]);
//     free(col);
//     free(eu);
//     free(ev);
//     free(qv);
//     free(qk);
//     free(out);
//     return 0;
// }
