/* Codeforces 2014/F - Sheriff's Defense */
// #include <stdio.h>
// #include <stdlib.h>
/* QCP_INSERT_BEGIN:P069_2014F_sheriffs_defense.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> list Z -> list (Z * Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P069_2014F_sheriffs_defense_lib */
/* QCP_INSERT_END:P069_2014F_sheriffs_defense.support */
static long long solver(int n, long long c, const long long *a, const int *eu,
                        const int *ev) /* QCP_INSERT_BEGIN:P069_2014F_sheriffs_defense.contract */

/*@ With (values : list Z)
             (e : list (Z * Z))
             (froms tos : list Z)
    Require
      1 <= Zlength(values) && Zlength(values) <= 200000 &&
      1 <= c && c <= 1000000000 &&
      Zlength(e) == Zlength(values) - 1 &&
      (forall i, (0 <= i && i < Zlength(e)) =>
        (1 <= fst(e[i]) && fst(e[i]) <= Zlength(values) &&
         1 <= snd(e[i]) && snd(e[i]) <= Zlength(values) &&
         fst(e[i]) != snd(e[i]))) &&
      n == Zlength(values) &&
      Zlength(froms) == n - 1 && Zlength(tos) == n - 1 &&
      (forall i, (0 <= i && i < n - 1) =>
        (fst(e[i]) == froms[i] + 1 &&
         snd(e[i]) == tos[i] + 1)) &&
      Int64Array::full(a, n, values) *
      IntArray::full(eu, n - 1, froms) *
      IntArray::full(ev, n - 1, tos)
    Ensure
      Spec(c, values, e, __return) &&
      Int64Array::full(a, n, values) *
      IntArray::full(eu, n - 1, froms) *
      IntArray::full(ev, n - 1, tos)
*/
/* QCP_INSERT_END:P069_2014F_sheriffs_defense.contract */
{
    int *head = malloc((size_t)n * sizeof(*head)), *to = malloc((size_t)(2 * n - 2) * sizeof(*to)),
        *nxt = malloc((size_t)(2 * n - 2) * sizeof(*nxt));
    for (int i = 0; i < n; ++i)
        head[i] = -1;
    int ec = 0;
    for (int i = 0; i < n - 1; ++i)
    {
        int u = eu[i], v = ev[i];
        to[ec] = v;
        nxt[ec] = head[u];
        head[u] = ec++;
        to[ec] = u;
        nxt[ec] = head[v];
        head[v] = ec++;
    }
    int *par = malloc((size_t)n * sizeof(*par)), *ord = malloc((size_t)n * sizeof(*ord));
    int cnt = 1;
    ord[0] = 0;
    par[0] = -1;
    for (int i = 0; i < cnt; ++i)
    {
        int v = ord[i];
        for (int e = head[v]; e != -1; e = nxt[e])
            if (to[e] != par[v])
            {
                par[to[e]] = v;
                ord[cnt++] = to[e];
            }
    }
    long long *d0 = calloc((size_t)n, sizeof(*d0)), *d1 = malloc((size_t)n * sizeof(*d1));
    for (int i = 0; i < n; ++i)
        d1[i] = a[i];
    for (int oi = n - 1; oi > 0; --oi)
    {
        int v = ord[oi], p = par[v];
        d0[p] += d0[v] > d1[v] ? d0[v] : d1[v];
        long long take = d1[v] - 2 * c;
        d1[p] += d0[v] > take ? d0[v] : take;
    }
    long long answer = d0[0] > d1[0] ? d0[0] : d1[0];
    free(head);
    free(to);
    free(nxt);
    free(par);
    free(ord);
    free(d0);
    free(d1);
    return answer;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n;
//         long long c;
//         scanf("%d %lld", &n, &c);
//         long long *a = malloc((size_t)n * sizeof(*a));
//         int *eu = malloc((size_t)(n - 1) * sizeof(*eu)),
//             *ev = malloc((size_t)(n - 1) * sizeof(*ev));
//         for (int i = 0; i < n; ++i)
//             scanf("%lld", &a[i]);
//         for (int i = 0; i < n - 1; ++i)
//         {
//             scanf("%d %d", &eu[i], &ev[i]);
//             --eu[i];
//             --ev[i];
//         }
//         printf("%lld\n", solver(n, c, a, eu, ev));
//         free(a);
//         free(eu);
//         free(ev);
//     }
//     return 0;
// }
