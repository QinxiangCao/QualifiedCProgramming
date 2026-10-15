/* Codeforces 1280/C - Jeremy Bearimy */
// #include <stdio.h>
// #include <stdlib.h>
typedef struct
{
    int to, next, w;
} Edge;
/* QCP_INSERT_BEGIN:P066_1280C_jeremy_bearimy.support */
/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Pre : Z -> list (Z * Z * Z) -> Prop)
      (Spec : Z -> list (Z * Z * Z) -> Z * Z -> Prop)
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P066_1280C_jeremy_bearimy_lib */
/* QCP_INSERT_END:P066_1280C_jeremy_bearimy.support */
static void solver(int k, const int *eu, const int *ev, const int *ew, long long *out_min,
                   long long *out_max) /* QCP_INSERT_BEGIN:P066_1280C_jeremy_bearimy.contract */

/*@ With (e : list (Z * Z * Z))
             (eu_data ev_data ew_data : list Z)
    Require
      1 <= k && k <= 100000 &&
      Zlength(e) == 2 * k - 1 &&
      (forall i, (0 <= i && i < Zlength(e)) =>
        (1 <= ztriple_1(e[i]) && ztriple_1(e[i]) <= 2 * k &&
         1 <= ztriple_2(e[i]) && ztriple_2(e[i]) <= 2 * k &&
         1 <= ztriple_3(e[i]) && ztriple_3(e[i]) <= 1000000)) &&
      Pre(k, e) &&
      Zlength(eu_data) == Zlength(e) && Zlength(ev_data) == Zlength(e) &&
      Zlength(ew_data) == Zlength(e) &&
      (forall i, (0 <= i && i < Zlength(e)) =>
        (eu_data[i] == ztriple_1(e[i]) && ev_data[i] == ztriple_2(e[i]) &&
         ew_data[i] == ztriple_3(e[i]))) &&
      IntArray::full(eu, Zlength(e), eu_data) *
      IntArray::full(ev, Zlength(e), ev_data) * IntArray::full(ew, Zlength(e), ew_data) *
      undef_data_at(out_min) * undef_data_at(out_max)
    Ensure
      exists minimum maximum,
        Spec(k, e, pair(minimum, maximum)) &&
        IntArray::full(eu, Zlength(e), eu_data) *
        IntArray::full(ev, Zlength(e), ev_data) * IntArray::full(ew, Zlength(e), ew_data) *
        store(out_min, long long, minimum) * store(out_max, long long, maximum)
*/
/* QCP_INSERT_END:P066_1280C_jeremy_bearimy.contract */
{
    int n = 2 * k, *head = malloc((size_t)n * sizeof(*head));
    for (int i = 0; i < n; ++i)
        head[i] = -1;
    Edge *e = malloc((size_t)(2 * n - 2) * sizeof(*e));
    int ec = 0;
    for (int i = 0; i < n - 1; ++i)
    {
        int u = eu[i], v = ev[i], w = ew[i];
        e[ec] = (Edge){v, head[u], w};
        head[u] = ec++;
        e[ec] = (Edge){u, head[v], w};
        head[v] = ec++;
    }
    int *par = malloc((size_t)n * sizeof(*par)), *pw = malloc((size_t)n * sizeof(*pw)),
        *ord = malloc((size_t)n * sizeof(*ord)), *sz = malloc((size_t)n * sizeof(*sz));
    int cnt = 1;
    ord[0] = 0;
    par[0] = -1;
    pw[0] = 0;
    for (int i = 0; i < cnt; ++i)
    {
        int v = ord[i];
        for (int z = head[v]; z != -1; z = e[z].next)
            if (e[z].to != par[v])
            {
                par[e[z].to] = v;
                pw[e[z].to] = e[z].w;
                ord[cnt++] = e[z].to;
            }
    }
    long long mn = 0, mx = 0;
    for (int i = 0; i < n; ++i)
        sz[i] = 1;
    for (int i = n - 1; i > 0; --i)
    {
        int v = ord[i];
        if (sz[v] & 1)
            mn += pw[v];
        int small = sz[v] < n - sz[v] ? sz[v] : n - sz[v];
        mx += (long long)small * pw[v];
        sz[par[v]] += sz[v];
    }
    *out_min = mn;
    *out_max = mx;
    free(head);
    free(e);
    free(par);
    free(pw);
    free(ord);
    free(sz);
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int k;
//         scanf("%d", &k);
//         int n = 2 * k, *eu = malloc((size_t)(n - 1) * sizeof(*eu)),
//             *ev = malloc((size_t)(n - 1) * sizeof(*ev)),
//             *ew = malloc((size_t)(n - 1) * sizeof(*ew));
//         for (int i = 0; i < n - 1; ++i)
//         {
//             scanf("%d %d %d", &eu[i], &ev[i], &ew[i]);
//             --eu[i];
//             --ev[i];
//         }
//         long long mn, mx;
//         solver(k, eu, ev, ew, &mn, &mx);
//         printf("%lld %lld\n", mn, mx);
//         free(eu);
//         free(ev);
//         free(ew);
//     }
//     return 0;
// }
