/* Codeforces 505/D - Mr. Kitayuta's Technology */
// #include <stdio.h>
// #include <stdlib.h>
static int find(int *p, int x)
{
    while (p[x] != x)
    {
        p[x] = p[p[x]];
        x = p[x];
    }
    return x;
}
/* QCP_INSERT_BEGIN:P079_505D_mr_kitayutas_technology.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : Z -> list (Z * Z) -> Prop)
      (Spec : Z -> list (Z * Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P079_505D_mr_kitayutas_technology_lib */
/* QCP_INSERT_END:P079_505D_mr_kitayutas_technology.support */
static long long
solver(int n, int m, const int *eu,
       const int *ev) /* QCP_INSERT_BEGIN:P079_505D_mr_kitayutas_technology.contract */

/*@ With (important : list (Z * Z))
             (eu_data ev_data : list Z)
    Require
      2 <= n && n <= 100000 &&
      1 <= Zlength(important) && Zlength(important) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(important)) => ((1 <= fst(important[i]) && fst(important[i]) <= n) && (1 <= snd(important[i]) && snd(important[i]) <= n) && (fst(important[i]) != snd(important[i])))) &&
      Pre(n, important) &&
      m == Zlength(important) && Zlength(eu_data) == m && Zlength(ev_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (eu_data[i] == fst(important[i]) && ev_data[i] == snd(important[i]))) &&
      IntArray::full(eu, m, eu_data) * IntArray::full(ev, m, ev_data)
    Ensure
      Spec(n, important, __return) &&
      IntArray::full(eu, m, eu_data) * IntArray::full(ev, m, ev_data)
*/
/* QCP_INSERT_END:P079_505D_mr_kitayutas_technology.contract */
{
    int *head = malloc((size_t)n * sizeof(*head)), *rhead = malloc((size_t)n * sizeof(*rhead)),
        *to = malloc((size_t)m * sizeof(*to)), *nxt = malloc((size_t)m * sizeof(*nxt)),
        *rto = malloc((size_t)m * sizeof(*rto)), *rnxt = malloc((size_t)m * sizeof(*rnxt)),
        *dsu = malloc((size_t)n * sizeof(*dsu));
    for (int i = 0; i < n; ++i)
    {
        head[i] = rhead[i] = -1;
        dsu[i] = i;
    }
    for (int i = 0; i < m; ++i)
    {
        int u = eu[i], v = ev[i];
        to[i] = v;
        nxt[i] = head[u];
        head[u] = i;
        rto[i] = u;
        rnxt[i] = rhead[v];
        rhead[v] = i;
        int a = find(dsu, u), b = find(dsu, v);
        if (a != b)
            dsu[a] = b;
    }
    unsigned char *vis = calloc((size_t)n, 1);
    int *iter = malloc((size_t)n * sizeof(*iter)), *stack = malloc((size_t)n * sizeof(*stack)),
        *order = malloc((size_t)n * sizeof(*order));
    int oc = 0;
    for (int s = 0; s < n; ++s)
        if (!vis[s])
        {
            int top = 0;
            stack[top++] = s;
            vis[s] = 1;
            iter[s] = head[s];
            while (top)
            {
                int v = stack[top - 1], e = iter[v];
                while (e != -1 && vis[to[e]])
                    e = nxt[e];
                iter[v] = e;
                if (e == -1)
                {
                    order[oc++] = v;
                    --top;
                }
                else
                {
                    iter[v] = nxt[e];
                    int u = to[e];
                    vis[u] = 1;
                    iter[u] = head[u];
                    stack[top++] = u;
                }
            }
        }
    int *comp = malloc((size_t)n * sizeof(*comp)), *csz = calloc((size_t)n, sizeof(*csz));
    for (int i = 0; i < n; ++i)
        comp[i] = -1;
    int cc = 0;
    for (int oi = n - 1; oi >= 0; --oi)
    {
        int s = order[oi];
        if (comp[s] >= 0)
            continue;
        int top = 0;
        stack[top++] = s;
        comp[s] = cc;
        while (top)
        {
            int v = stack[--top];
            ++csz[cc];
            for (int e = rhead[v]; e != -1; e = rnxt[e])
                if (comp[rto[e]] < 0)
                {
                    comp[rto[e]] = cc;
                    stack[top++] = rto[e];
                }
        }
        ++cc;
    }
    int *weak_size = calloc((size_t)n, sizeof(*weak_size));
    unsigned char *has_cycle = calloc((size_t)n, 1);
    for (int v = 0; v < n; ++v)
    {
        int root = find(dsu, v);
        ++weak_size[root];
        if (csz[comp[v]] > 1)
            has_cycle[root] = 1;
    }
    long long ans = 0;
    for (int v = 0; v < n; ++v)
        if (find(dsu, v) == v)
            ans += weak_size[v] - 1 + has_cycle[v];
    free(head);
    free(rhead);
    free(to);
    free(nxt);
    free(rto);
    free(rnxt);
    free(dsu);
    free(vis);
    free(iter);
    free(stack);
    free(order);
    free(comp);
    free(csz);
    free(weak_size);
    free(has_cycle);
    return ans;
}
// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     int *eu = malloc((size_t)m * sizeof(*eu)), *ev = malloc((size_t)m * sizeof(*ev));
//     for (int i = 0; i < m; ++i)
//     {
//         scanf("%d %d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     printf("%lld\n", solver(n, m, eu, ev));
//     free(eu);
//     free(ev);
//     return 0;
// }
