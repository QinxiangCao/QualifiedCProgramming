/* Codeforces 1704/E - Count Seconds */
// #include <stdio.h>
// #include <stdlib.h>
#define MOD 998244353LL
/* QCP_INSERT_BEGIN:P077_1704E_count_seconds.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : list Z -> list (Z * Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P077_1704E_count_seconds_lib */
/* QCP_INSERT_END:P077_1704E_count_seconds.support */
static long long solver(int n, int m, const long long *input, const int *eu,
                        const int *ev) /* QCP_INSERT_BEGIN:P077_1704E_count_seconds.contract */

/*@ With (a : list Z)
             (edges : list (Z * Z))
             (froms tos : list Z)
    Require
      1 <= Zlength(a) && Zlength(a) <= 1000 &&
      1 <= Zlength(edges) && Zlength(edges) <= 1000 &&
      (forall i, (0 <= i && i < Zlength(a)) => (0 <= a[i] && a[i] <= 1000000000)) &&
      n == Zlength(a) && m == Zlength(edges) &&
      Zlength(froms) == m && Zlength(tos) == m &&
      (forall i, (0 <= i && i < m) =>
        (fst(edges[i]) == froms[i] + 1 &&
         snd(edges[i]) == tos[i] + 1)) &&
      Int64Array::full(input, n, a) *
      IntArray::full(eu, m, froms) *
      IntArray::full(ev, m, tos)
    Ensure
      Spec(a, edges, __return) &&
      Int64Array::full(input, n, a) *
      IntArray::full(eu, m, froms) *
      IntArray::full(ev, m, tos)
*/
/* QCP_INSERT_END:P077_1704E_count_seconds.contract */
{
    long long *a = malloc((size_t)n * sizeof(*a)), *nexta = malloc((size_t)n * sizeof(*nexta));
    for (int i = 0; i < n; ++i)
        a[i] = input[i];
    int *head = malloc((size_t)n * sizeof(*head)), *to = malloc((size_t)m * sizeof(*to)),
        *nxt = malloc((size_t)m * sizeof(*nxt)), *indeg = calloc((size_t)n, sizeof(*indeg));
    for (int i = 0; i < n; ++i)
        head[i] = -1;
    for (int i = 0; i < m; ++i)
    {
        int u = eu[i], v = ev[i];
        to[i] = v;
        nxt[i] = head[u];
        head[u] = i;
        ++indeg[v];
    }
    int done = 0, time = 0;
    for (; time < n; ++time)
    {
        int any = 0;
        for (int i = 0; i < n; ++i)
        {
            nexta[i] = a[i];
            if (a[i] > 0)
                any = 1;
        }
        if (!any)
        {
            done = 1;
            break;
        }
        for (int v = 0; v < n; ++v)
            if (a[v] > 0)
            {
                --nexta[v];
                for (int e = head[v]; e != -1; e = nxt[e])
                    ++nexta[to[e]];
            }
        long long *tmp = a;
        a = nexta;
        nexta = tmp;
    }
    long long ans;
    if (done)
        ans = time;
    else
    {
        int *q = malloc((size_t)n * sizeof(*q)), l = 0, r = 0;
        for (int i = 0; i < n; ++i)
            if (indeg[i] == 0)
                q[r++] = i;
        int *ord = malloc((size_t)n * sizeof(*ord)), oc = 0;
        while (l < r)
        {
            int v = q[l++];
            ord[oc++] = v;
            for (int e = head[v]; e != -1; e = nxt[e])
                if (--indeg[to[e]] == 0)
                    q[r++] = to[e];
        }
        long long *dp = calloc((size_t)n, sizeof(*dp));
        for (int i = n - 1; i >= 0; --i)
        {
            int v = ord[i];
            if (head[v] == -1)
                dp[v] = 1;
            else
                for (int e = head[v]; e != -1; e = nxt[e])
                    dp[v] = (dp[v] + dp[to[e]]) % MOD;
        }
        ans = n % MOD;
        for (int i = 0; i < n; ++i)
            ans = (ans + (a[i] % MOD) * dp[i]) % MOD;
        free(q);
        free(ord);
        free(dp);
    }
    free(a);
    free(nexta);
    free(head);
    free(to);
    free(nxt);
    free(indeg);
    return ans;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n, m;
//         scanf("%d %d", &n, &m);
//         long long *a = malloc((size_t)n * sizeof(*a));
//         int *eu = malloc((size_t)m * sizeof(*eu)), *ev = malloc((size_t)m * sizeof(*ev));
//         for (int i = 0; i < n; ++i)
//             scanf("%lld", &a[i]);
//         for (int i = 0; i < m; ++i)
//         {
//             scanf("%d %d", &eu[i], &ev[i]);
//             --eu[i];
//             --ev[i];
//         }
//         printf("%lld\n", solver(n, m, a, eu, ev));
//         free(a);
//         free(eu);
//         free(ev);
//     }
//     return 0;
// }
