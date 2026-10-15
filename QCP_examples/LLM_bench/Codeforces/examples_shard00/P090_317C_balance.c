// #include <stdio.h>
// #include <stdlib.h>
typedef long long i64;
typedef struct
{
    int to, next;
} Edge;
typedef struct
{
    int u, v;
    i64 rem;
} Flow;
typedef struct
{
    int u, v;
    i64 d;
} Op;
/* QCP_INSERT_BEGIN:P090_317C_balance.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (merge_int64_by_ints : Z -> Z -> Z -> Prop)
      (Spec : Z -> list Z -> list Z -> list (Z * Z) -> option (list (Z * Z * Z)) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P090_317C_balance_lib */
/* QCP_INSERT_END:P090_317C_balance.support */
static int solver(int n, i64 cap, int e, const i64 *initial, const i64 *goal, const int *eu,
                  const int *ev, Op *ops) /* QCP_INSERT_BEGIN:P090_317C_balance.contract */

/*@ With (capacity : Z)
             (initial_data : list Z)
             (target : list Z)
             (tubes : list (Z * Z))
             (froms tos : list Z)
    Require
      1 <= Zlength(initial_data) && Zlength(initial_data) <= 300 &&
      Zlength(target) == Zlength(initial_data) &&
      1 <= capacity && capacity <= 1000000000 &&
      Zlength(tubes) <= 50000 &&
      (forall i, (0 <= i && i < Zlength(initial_data)) => (0 <= initial_data[i] && initial_data[i] <= capacity)) &&
      (forall i, (0 <= i && i < Zlength(target)) => (0 <= target[i] && target[i] <= capacity)) &&
      n == Zlength(initial_data) && e == Zlength(tubes) &&
      Zlength(froms) == e && Zlength(tos) == e &&
      (forall i, (0 <= i && i < e) =>
        (fst(tubes[i]) == froms[i] + 1 &&
         snd(tubes[i]) == tos[i] + 1)) &&
      Int64Array::full(initial, n, initial_data) *
      Int64Array::full(goal, n, target) *
      IntArray::full(eu, e, froms) *
      IntArray::full(ev, e, tos) *
      IntArray::undef_full(ops, 4 * (2 * n * n + 1))
    Ensure
      exists ops_mem,
        ((__return == -1 && Spec(capacity, initial_data, target, tubes, None)) ||
         (exists moves dlo dhi,
            Spec(capacity, initial_data, target, tubes, Some(moves)) &&
            __return == Zlength(moves) &&
            Zlength(dlo) == __return && Zlength(dhi) == __return &&
            (forall i, (0 <= i && i < __return) =>
              (ops_mem[4 * i] == Some(ztriple_1(moves[i]) - 1) &&
               ops_mem[4 * i + 1] == Some(ztriple_2(moves[i]) - 1) &&
               ops_mem[4 * i + 2] == Some(dlo[i]) &&
               ops_mem[4 * i + 3] == Some(dhi[i]) &&
               merge_int64_by_ints(dlo[i], dhi[i], ztriple_3(moves[i])))))) &&
        Int64Array::full(initial, n, initial_data) * Int64Array::full(goal, n, target) *
        IntArray::full(eu, e, froms) * IntArray::full(ev, e, tos) *
        IntArray::mixed_full(ops, 4 * (2 * n * n + 1), ops_mem)
*/
/* QCP_INSERT_END:P090_317C_balance.contract */
{
    i64 *cur = malloc(n * sizeof *cur);
    for (int i = 0; i < n; i++)
        cur[i] = initial[i];
    int *head = malloc(n * sizeof *head);
    for (int i = 0; i < n; i++)
        head[i] = -1;
    Edge *ed = malloc((size_t)(2 * e) * sizeof *ed);
    int ec = 0;
    for (int i = 0; i < e; i++)
    {
        int u = eu[i], v = ev[i];
        ed[ec] = (Edge){v, head[u]};
        head[u] = ec++;
        ed[ec] = (Edge){u, head[v]};
        head[v] = ec++;
    }
    int *par = malloc(n * sizeof *par), *ord = malloc(n * sizeof *ord),
        *comp = malloc(n * sizeof *comp);
    for (int i = 0; i < n; i++)
        par[i] = -2;
    int os = 0, cc = 0;
    for (int r = 0; r < n; r++)
        if (par[r] == -2)
        {
            int start = os;
            par[r] = -1;
            comp[r] = cc;
            ord[os++] = r;
            for (int z = start; z < os; z++)
            {
                int v = ord[z];
                for (int x = head[v]; x != -1; x = ed[x].next)
                {
                    int u = ed[x].to;
                    if (par[u] != -2)
                        continue;
                    par[u] = v;
                    comp[u] = cc;
                    ord[os++] = u;
                }
            }
            cc++;
        }
    i64 *bal = malloc(n * sizeof *bal), *sumA = calloc((size_t)cc, sizeof *sumA),
        *sumB = calloc((size_t)cc, sizeof *sumB);
    for (int i = 0; i < n; i++)
    {
        bal[i] = cur[i] - goal[i];
        sumA[comp[i]] += cur[i];
        sumB[comp[i]] += goal[i];
    }
    int possible = 1;
    for (int i = 0; i < cc; i++)
        if (sumA[i] != sumB[i])
            possible = 0;
    for (int i = n - 1; i >= 0 && possible; i--)
    {
        int v = ord[i];
        if (par[v] >= 0)
            bal[par[v]] += bal[v];
    }
    Flow *f = malloc((size_t)(n - cc) * sizeof *f);
    int fc = 0;
    if (possible)
        for (int v = 0; v < n; v++)
            if (par[v] >= 0)
            {
                if (bal[v] > 0)
                    f[fc++] = (Flow){v, par[v], bal[v]};
                else if (bal[v] < 0)
                    f[fc++] = (Flow){par[v], v, -bal[v]};
            }
    int maxop = 2 * n * n, oc = 0, left = fc;
    while (possible && left)
    {
        int progress = 0;
        for (int i = 0; i < fc; i++)
            if (f[i].rem)
            {
                i64 d = f[i].rem;
                if (d > cur[f[i].u])
                    d = cur[f[i].u];
                i64 room = cap - cur[f[i].v];
                if (d > room)
                    d = room;
                if (d > 0)
                {
                    cur[f[i].u] -= d;
                    cur[f[i].v] += d;
                    f[i].rem -= d;
                    ops[oc++] = (Op){f[i].u, f[i].v, d};
                    progress = 1;
                    if (!f[i].rem)
                        left--;
                }
            }
        if (!progress || oc > maxop)
            possible = 0;
    }
    free(f);
    free(sumB);
    free(sumA);
    free(bal);
    free(comp);
    free(ord);
    free(par);
    free(ed);
    free(head);
    free(cur);
    return possible ? oc : -1;
}
// int main(void)
// {
//     int n, e;
//     i64 cap;
//     if (scanf("%d%lld%d", &n, &cap, &e) != 3)
//         return 0;
//     i64 *cur = malloc(n * sizeof *cur), *goal = malloc(n * sizeof *goal);
//     int *eu = malloc((size_t)e * sizeof *eu), *ev = malloc((size_t)e * sizeof *ev);
//     for (int i = 0; i < n; i++)
//         scanf("%lld", &cur[i]);
//     for (int i = 0; i < n; i++)
//         scanf("%lld", &goal[i]);
//     for (int i = 0; i < e; i++)
//     {
//         scanf("%d%d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     Op *ops = malloc((size_t)(2 * n * n + 1) * sizeof *ops);
//     int oc = solver(n, cap, e, cur, goal, eu, ev, ops);
//     if (oc < 0)
//         puts("NO");
//     else
//     {
//         printf("%d\n", oc);
//         for (int i = 0; i < oc; i++)
//             printf("%d %d %lld\n", ops[i].u + 1, ops[i].v + 1, ops[i].d);
//     }
//     free(ops);
//     free(ev);
//     free(eu);
//     free(goal);
//     free(cur);
//     return 0;
// }
