/* Codeforces 1039/C - Network Safety */
// #include <stdio.h>
// #include <stdlib.h>
// #include <stdint.h>
#define MOD 1000000007LL
typedef struct
{
    uint64_t x;
    int u, v;
} Edge;
static int cmp_edge(const void *a, const void *b)
{
    uint64_t x = ((const Edge *)a)->x, y = ((const Edge *)b)->x;
    return (x > y) - (x < y);
}
static int find(int *p, int x)
{
    while (p[x] != x)
    {
        p[x] = p[p[x]];
        x = p[x];
    }
    return x;
}
static long long modpow(long long a, uint64_t e)
{
    long long r = 1;
    while (e)
    {
        if (e & 1)
            r = r * a % MOD;
        a = a * a % MOD;
        e >>= 1;
    }
    return r;
}
/* QCP_INSERT_BEGIN:P076_1039C_network_safety.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Zpow : Z -> Z -> Z)
      (Pre : Z -> list Z -> list (Z * Z) -> Prop)
      (Spec : Z -> list Z -> list (Z * Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (UInt64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P076_1039C_network_safety_lib */
/* QCP_INSERT_END:P076_1039C_network_safety.support */
static long long solver(int n, int m, int k, const uint64_t *c, const int *eu,
                        const int *ev) /* QCP_INSERT_BEGIN:P076_1039C_network_safety.contract */

/*@ With (keys : list Z)
             (edges : list (Z * Z))
             (froms tos : list Z)
    Require
      0 <= k && k <= 60 &&
      1 <= Zlength(keys) && Zlength(keys) <= 500000 &&
      Zlength(edges) <= 500000 &&
      (forall i, (0 <= i && i < Zlength(keys)) => (0 <= keys[i] && keys[i] < Zpow(2, k))) &&
      (forall i, (0 <= i && i < Zlength(edges)) => ((1 <= fst(edges[i]) && fst(edges[i]) <= Zlength(keys)) && (1 <= snd(edges[i]) && snd(edges[i]) <= Zlength(keys)) && (fst(edges[i]) != snd(edges[i])))) &&
      Pre(k, keys, edges) &&
      n == Zlength(keys) && m == Zlength(edges) &&
      Zlength(froms) == m && Zlength(tos) == m &&
      (forall i, (0 <= i && i < m) =>
        (fst(edges[i]) == froms[i] + 1 &&
         snd(edges[i]) == tos[i] + 1)) &&
      UInt64Array::full(c, n, keys) *
      IntArray::full(eu, m, froms) *
      IntArray::full(ev, m, tos)
    Ensure
      Spec(k, keys, edges, __return) &&
      UInt64Array::full(c, n, keys) *
      IntArray::full(eu, m, froms) *
      IntArray::full(ev, m, tos)
*/
/* QCP_INSERT_END:P076_1039C_network_safety.contract */
{
    Edge *e = malloc((size_t)m * sizeof(*e));
    for (int i = 0; i < m; ++i)
    {
        e[i].u = eu[i];
        e[i].v = ev[i];
        e[i].x = c[e[i].u] ^ c[e[i].v];
    }
    qsort(e, (size_t)m, sizeof(*e), cmp_edge);
    int *p = malloc((size_t)n * sizeof(*p)), *seen = calloc((size_t)n, sizeof(*seen));
    for (int i = 0; i < n; ++i)
        p[i] = i;
    long long ans = 0;
    uint64_t groups = 0;
    for (int i = 0; i < m;)
    {
        int j = i, unions = 0, touched_count = 0;
        int *touched = malloc((size_t)2 * (m - i) * sizeof(*touched));
        while (j < m && e[j].x == e[i].x)
        {
            int vs[2] = {e[j].u, e[j].v};
            for (int z = 0; z < 2; ++z)
                if (!seen[vs[z]])
                {
                    seen[vs[z]] = 1;
                    p[vs[z]] = vs[z];
                    touched[touched_count++] = vs[z];
                }
            int x = find(p, e[j].u), y = find(p, e[j].v);
            if (x != y)
            {
                p[x] = y;
                ++unions;
            }
            ++j;
        }
        ans = (ans + modpow(2, (uint64_t)(n - unions))) % MOD;
        ++groups;
        for (int z = 0; z < touched_count; ++z)
            seen[touched[z]] = 0;
        free(touched);
        i = j;
    }
    uint64_t total_values = k == 64 ? 0 : (1ULL << k);
    long long absent = ((total_values % MOD) - (groups % MOD) + MOD) % MOD;
    ans = (ans + absent * modpow(2, (uint64_t)n)) % MOD;
    free(e);
    free(p);
    free(seen);
    return ans;
}
// int main(void)
// {
//     int n, m, k;
//     if (scanf("%d %d %d", &n, &m, &k) != 3)
//         return 0;
//     uint64_t *c = malloc((size_t)n * sizeof(*c));
//     int *eu = malloc((size_t)m * sizeof(*eu)), *ev = malloc((size_t)m * sizeof(*ev));
//     for (int i = 0; i < n; ++i)
//         scanf("%llu", (unsigned long long *)&c[i]);
//     for (int i = 0; i < m; ++i)
//     {
//         scanf("%d %d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     printf("%lld\n", solver(n, m, k, c, eu, ev));
//     free(c);
//     free(eu);
//     free(ev);
//     return 0;
// }
