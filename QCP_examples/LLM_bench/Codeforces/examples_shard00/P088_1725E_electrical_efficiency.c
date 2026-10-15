// #include <stdio.h>
// #include <stdlib.h>
#include "array2_ext_def.h"
#define LOG 19
#define MOD 998244353LL
typedef long long i64;
typedef struct
{
    int to, next;
} Edge;
typedef struct
{
    int p, v;
} Pair;
static int *tin, *tout, *dep, (*up)[LOG];
static int cmppair(const void *A, const void *B)
{
    const Pair *a = A, *b = B;
    return a->p == b->p ? a->v - b->v : a->p - b->p;
}
static int cmpvertex(const void *A, const void *B)
{
    int a = *(const int *)A, b = *(const int *)B;
    return tin[a] - tin[b];
}
static int anc(int a, int b)
{
    return tin[a] <= tin[b] && tout[b] <= tout[a];
}
static int lca(int a, int b)
{
    if (anc(a, b))
        return a;
    if (anc(b, a))
        return b;
    for (int j = LOG - 1; j >= 0; j--)
        if (!anc(up[a][j], b))
            a = up[a][j];
    return up[a][0];
}
static i64 c3(i64 x)
{
    return x < 3 ? 0 : x * (x - 1) * (x - 2) / 6;
}
/* QCP_INSERT_BEGIN:P088_1725E_electrical_efficiency.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : list Z -> list (Z * Z) -> Prop)
      (Spec : list Z -> list (Z * Z) -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P088_1725E_electrical_efficiency_lib */
/* QCP_INSERT_END:P088_1725E_electrical_efficiency.support */
static i64 solver(int n, const int *input, const int *eu,
                  const int *ev) /* QCP_INSERT_BEGIN:P088_1725E_electrical_efficiency.contract */

/*@ With (coefficients : list Z)
             (edges : list (Z * Z))
             (eu_data ev_data : list Z)
    Require
      1 <= Zlength(coefficients) && Zlength(coefficients) <= 200000 &&
      Zlength(edges) == Zlength(coefficients)-1 &&
      (forall i, (0 <= i && i < Zlength(coefficients)) => (1 <= coefficients[i] && coefficients[i] <= 200000)) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (1 <= fst(edges[i]) && fst(edges[i]) <= Zlength(coefficients) &&
         1 <= snd(edges[i]) && snd(edges[i]) <= Zlength(coefficients))) &&
      Pre(coefficients, edges) &&
      n == Zlength(coefficients) &&
      Zlength(eu_data) == Zlength(edges) && Zlength(ev_data) == Zlength(edges) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (eu_data[i] == fst(edges[i]) && ev_data[i] == snd(edges[i]))) &&
      IntArray::full(input, n, coefficients) *
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data)
    Ensure
      Spec(coefficients, edges, __return) &&
      IntArray::full(input, n, coefficients) *
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data)
*/
/* QCP_INSERT_END:P088_1725E_electrical_efficiency.contract */
{
    int *a = malloc(n * sizeof *a), maxa = 1;
    for (int i = 0; i < n; i++)
    {
        a[i] = input[i];
        if (a[i] > maxa)
            maxa = a[i];
    }
    int *head = malloc(n * sizeof *head);
    for (int i = 0; i < n; i++)
        head[i] = -1;
    Edge *ed = malloc((size_t)(2 * n) * sizeof *ed);
    int ec = 0;
    for (int i = 0; i < n - 1; i++)
    {
        int u = eu[i], v = ev[i];
        ed[ec] = (Edge){v, head[u]};
        head[u] = ec++;
        ed[ec] = (Edge){u, head[v]};
        head[v] = ec++;
    }
    int *spf = calloc((size_t)maxa + 1, sizeof *spf);
    for (int i = 2; i <= maxa; i++)
        if (!spf[i])
        {
            spf[i] = i;
            if ((i64)i * i <= maxa)
                for (int j = i * i; j <= maxa; j += i)
                    if (!spf[j])
                        spf[j] = i;
        }
    int cap = n * 8 + 1, pc = 0;
    Pair *pa = malloc((size_t)cap * sizeof *pa);
    for (int v = 0; v < n; v++)
    {
        int x = a[v];
        while (x > 1)
        {
            int p = spf[x];
            if (pc == cap)
            {
                cap *= 2;
                pa = realloc(pa, (size_t)cap * sizeof *pa);
            }
            pa[pc++] = (Pair){p, v};
            while (x % p == 0)
                x /= p;
        }
    }
    qsort(pa, pc, sizeof *pa, cmppair);
    tin = malloc(n * sizeof *tin);
    tout = malloc(n * sizeof *tout);
    dep = malloc(n * sizeof *dep);
    up = malloc((size_t)n * sizeof *up);
    int *it = malloc(n * sizeof *it), *st = malloc(n * sizeof *st), *par = malloc(n * sizeof *par);
    int timer = 0, sp = 0;
    st[sp++] = 0;
    par[0] = 0;
    dep[0] = 0;
    it[0] = head[0];
    tin[0] = timer++;
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
        dep[u] = dep[v] + 1;
        tin[u] = timer++;
        it[u] = head[u];
        st[sp++] = u;
    }
    for (int v = 0; v < n; v++)
    {
        up[v][0] = par[v];
        for (int j = 1; j < LOG; j++)
            up[v][j] = up[up[v][j - 1]][j - 1];
    }
    int *mark = calloc(n, sizeof *mark), stamp = 0;
    i64 answer = 0;
    for (int lo = 0; lo < pc;)
    {
        int hi = lo + 1;
        while (hi < pc && pa[hi].p == pa[lo].p)
            hi++;
        int s = hi - lo;
        if (s >= 3)
        {
            int *vs = malloc((size_t)(2 * s) * sizeof *vs);
            for (int j = 0; j < s; j++)
                vs[j] = pa[lo + j].v;
            qsort(vs, s, sizeof *vs, cmpvertex);
            int z = s;
            for (int j = 1; j < s; j++)
                vs[z++] = lca(vs[j - 1], vs[j]);
            qsort(vs, z, sizeof *vs, cmpvertex);
            int nz = 0;
            for (int j = 0; j < z; j++)
                if (!nz || vs[j] != vs[nz - 1])
                    vs[nz++] = vs[j];
            ++stamp;
            for (int j = lo; j < hi; j++)
                mark[pa[j].v] = stamp;
            int *vp = malloc((size_t)nz * sizeof *vp), *cnt = malloc((size_t)nz * sizeof *cnt),
                *stack = malloc((size_t)nz * sizeof *stack);
            int ss = 0;
            vp[0] = -1;
            stack[ss++] = 0;
            for (int j = 1; j < nz; j++)
            {
                while (ss && !anc(vs[stack[ss - 1]], vs[j]))
                    ss--;
                vp[j] = stack[ss - 1];
                stack[ss++] = j;
            }
            for (int j = 0; j < nz; j++)
                cnt[j] = mark[vs[j]] == stamp;
            i64 all = c3(s);
            for (int j = nz - 1; j > 0; j--)
            {
                int p = vp[j];
                i64 x = cnt[j];
                i64 ways = all - c3(x) - c3(s - x);
                i64 len = dep[vs[j]] - dep[vs[p]];
                answer = (answer + (len % MOD) * (ways % MOD)) % MOD;
                cnt[p] += cnt[j];
            }
            free(stack);
            free(cnt);
            free(vp);
            free(vs);
        }
        lo = hi;
    }
    i64 result = answer % MOD;
    free(mark);
    free(par);
    free(st);
    free(it);
    free(up);
    free(dep);
    free(tout);
    free(tin);
    free(pa);
    free(spf);
    free(ed);
    free(head);
    free(a);
    return result;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     int *a = malloc(n * sizeof *a), *eu = malloc((size_t)(n - 1) * sizeof *eu),
//         *ev = malloc((size_t)(n - 1) * sizeof *ev);
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     for (int i = 0; i < n - 1; i++)
//     {
//         scanf("%d%d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     printf("%lld\n", solver(n, a, eu, ev));
//     free(a);
//     free(eu);
//     free(ev);
//     return 0;
// }
