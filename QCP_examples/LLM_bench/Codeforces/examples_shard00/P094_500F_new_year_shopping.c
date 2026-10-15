// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"
#include "array2_ext_def.h"
typedef struct
{
    int c, h;
} Item;
typedef struct
{
    Item *a;
    int n, cap;
} Vec;
typedef struct
{
    int t, b, id, next;
} Query;
static Vec *seg;
static int *dp, *ans, *head;
static Query *qs;
static int U;
static void push(Vec *v, Item x)
{
    if (v->n == v->cap)
    {
        v->cap = v->cap ? 2 * v->cap : 2;
        v->a = realloc(v->a, (size_t)v->cap * sizeof *v->a);
    }
    v->a[v->n++] = x;
}
static void add(int o, int l, int r, int ql, int qr, Item x)
{
    if (ql <= l && r <= qr)
    {
        push(&seg[o], x);
        return;
    }
    int md = (l + r) / 2;
    if (ql <= md)
        add(o * 2, l, md, ql, qr, x);
    if (qr > md)
        add(o * 2 + 1, md + 1, r, ql, qr, x);
}
static int lower(int *a, int n, int x)
{
    int l = 0, r = n;
    while (l < r)
    {
        int m = (l + r) / 2;
        if (a[m] < x)
            l = m + 1;
        else
            r = m;
    }
    return l;
}
static int upper(int *a, int n, int x)
{
    int l = 0, r = n;
    while (l < r)
    {
        int m = (l + r) / 2;
        if (a[m] <= x)
            l = m + 1;
        else
            r = m;
    }
    return l;
}
static int backup[20][4001];
static void solve(int o, int l, int r, int dep)
{
    int changed = seg[o].n > 0;
    if (changed)
        memcpy(backup[dep], dp, 4001 * sizeof(int));
    for (int z = 0; z < seg[o].n; z++)
    {
        int c = seg[o].a[z].c, h = seg[o].a[z].h;
        for (int b = 4000; b >= c; b--)
            if (dp[b - c] + h > dp[b])
                dp[b] = dp[b - c] + h;
    }
    if (l == r)
    {
        for (int x = head[l]; x != -1; x = qs[x].next)
            ans[qs[x].id] = dp[qs[x].b];
    }
    else
    {
        int md = (l + r) / 2;
        solve(o * 2, l, md, dep + 1);
        solve(o * 2 + 1, md + 1, r, dep + 1);
    }
    if (changed)
        memcpy(dp, backup[dep], 4001 * sizeof(int));
}
static int cmpi(const void *A, const void *B)
{
    return *(const int *)A - *(const int *)B;
}
/* QCP_INSERT_BEGIN:P094_500F_new_year_shopping.support */
/*@ Extern Coq
      (Spec : Z -> list (Z * Z * Z) -> list (Z * Z) -> list Z -> Prop)
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (IntArray2::full_shape : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P094_500F_new_year_shopping_lib */
/* QCP_INSERT_END:P094_500F_new_year_shopping.support */
static void solver(int n, int p, const int *c, const int *h, const int *t, int q, const int *qt,
                   const int *qb,
                   int *out) /* QCP_INSERT_BEGIN:P094_500F_new_year_shopping.contract */

/*@ With (items : list (Z * Z * Z))
             (queries : list (Z * Z))
             (c_data h_data t_data qt_data qb_data : list Z)
    Require
      1 <= p && p <= 10000 &&
      1 <= Zlength(items) && Zlength(items) <= 4000 &&
      1 <= Zlength(queries) && Zlength(queries) <= 20000 &&
      n == Zlength(items) && q == Zlength(queries) &&
      Zlength(c_data) == n && Zlength(h_data) == n && Zlength(t_data) == n &&
      Zlength(qt_data) == q && Zlength(qb_data) == q &&
      (forall i, (0 <= i && i < n) =>
        (c_data[i] == ztriple_1(items[i]) && h_data[i] == ztriple_2(items[i]) &&
         t_data[i] == ztriple_3(items[i]))) &&
      (forall i, (0 <= i && i < q) =>
        (qt_data[i] == fst(queries[i]) && qb_data[i] == snd(queries[i]))) &&
      IntArray::full(c, n, c_data) * IntArray::full(h, n, h_data) *
      IntArray::full(t, n, t_data) * IntArray::full(qt, q, qt_data) *
      IntArray::full(qb, q, qb_data) * IntArray::undef_full(out, q) *
      IntArray2::full_shape(backup, 20, 4001)
    Ensure
      exists result,
        Spec(p, items, queries, result) &&
        Zlength(result) == q &&
        IntArray::full(c, n, c_data) * IntArray::full(h, n, h_data) *
        IntArray::full(t, n, t_data) * IntArray::full(qt, q, qt_data) *
        IntArray::full(qb, q, qb_data) * IntArray::full(out, q, result) *
        IntArray2::full_shape(backup, 20, 4001)
*/
/* QCP_INSERT_END:P094_500F_new_year_shopping.contract */
{
    qs = malloc(q * sizeof *qs);
    int *times = malloc(q * sizeof *times);
    for (int i = 0; i < q; i++)
    {
        qs[i].t = qt[i];
        qs[i].b = qb[i];
        qs[i].id = i;
        times[i] = qs[i].t;
    }
    qsort(times, q, sizeof *times, cmpi);
    U = 0;
    for (int i = 0; i < q; i++)
        if (!U || times[i] != times[U - 1])
            times[U++] = times[i];
    seg = calloc((size_t)4 * U + 5, sizeof *seg);
    for (int i = 0; i < n; i++)
    {
        int l = lower(times, U, t[i]), r = upper(times, U, t[i] + p - 1) - 1;
        if (l <= r)
            add(1, 0, U - 1, l, r, (Item){c[i], h[i]});
    }
    head = malloc(U * sizeof *head);
    for (int i = 0; i < U; i++)
        head[i] = -1;
    for (int i = 0; i < q; i++)
    {
        int x = lower(times, U, qs[i].t);
        qs[i].next = head[x];
        head[x] = i;
    }
    dp = calloc(4001, sizeof *dp);
    ans = malloc(q * sizeof *ans);
    solve(1, 0, U - 1, 0);
    for (int i = 0; i < q; i++)
        out[i] = ans[i];
    for (int i = 0; i < 4 * U + 5; i++)
        free(seg[i].a);
    free(ans);
    free(dp);
    free(head);
    free(seg);
    free(times);
    free(qs);
    ans = dp = head = NULL;
    seg = NULL;
    qs = NULL;
}
// int main(void)
// {
//     int n, p;
//     if (scanf("%d%d", &n, &p) != 2)
//         return 0;
//     int *c = malloc(n * sizeof *c), *h = malloc(n * sizeof *h), *t = malloc(n * sizeof *t);
//     for (int i = 0; i < n; i++)
//         scanf("%d%d%d", &c[i], &h[i], &t[i]);
//     int q;
//     scanf("%d", &q);
//     int *qt = malloc(q * sizeof *qt), *qb = malloc(q * sizeof *qb), *out = malloc(q * sizeof *out);
//     for (int i = 0; i < q; i++)
//         scanf("%d%d", &qt[i], &qb[i]);
//     solver(n, p, c, h, t, q, qt, qb, out);
//     for (int i = 0; i < q; i++)
//         printf("%d\n", out[i]);
//     free(out);
//     free(qb);
//     free(qt);
//     free(t);
//     free(h);
//     free(c);
//     return 0;
// }
