/* Codeforces 276/E - Little Girl and Problem on Trees */
// #include <stdio.h>
// #include <stdlib.h>
static long long *branch_bit, *depth_bit, root_value;
static int total_nodes;
static void add(long long *b, int i, long long x)
{
    for (; i <= total_nodes + 1; i += i & -i)
        b[i] += x;
}
static long long get(long long *b, int i)
{
    long long s = 0;
    for (; i; i -= i & -i)
        s += b[i];
    return s;
}
static void range_add(long long *b, int l, int r, long long x)
{
    if (l > r)
        return;
    add(b, l, x);
    add(b, r + 1, -x);
}
typedef struct
{
    int type, v, d;
    long long x;
} Query;
/* QCP_INSERT_BEGIN:P072_276E_little_girl_and_problem_on_trees.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (merge_int64_by_ints : Z -> Z -> Z -> Prop)
      (Spec : Z -> list (Z * Z) -> list (list Z) -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P072_276E_little_girl_and_problem_on_trees_lib */
/* QCP_INSERT_END:P072_276E_little_girl_and_problem_on_trees.support */
static int
solver(int n, const int *eu, const int *ev, int q, const Query *queries,
       long long *out) /* QCP_INSERT_BEGIN:P072_276E_little_girl_and_problem_on_trees.contract */

/*@ With (edges : list (Z * Z))
             (requests : list (list Z))
             (froms tos xlo xhi : list Z)
             (query_mem : list (option Z))
    Require
      2 <= n && n <= 100000 &&
      Zlength(edges) == n - 1 &&
      1 <= Zlength(requests) && Zlength(requests) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(requests)) => (((Zlength(Znth(i, requests, nil)) == 4) && (Znth(0, Znth(i, requests, nil), 0) == 0) && (1 <= Znth(1, Znth(i, requests, nil), 0) && Znth(1, Znth(i, requests, nil), 0) <= n) && (1 <= Znth(2, Znth(i, requests, nil), 0) && Znth(2, Znth(i, requests, nil), 0) <= 10000) && (1 <= Znth(3, Znth(i, requests, nil), 0) && Znth(3, Znth(i, requests, nil), 0) < n)) || ((Zlength(Znth(i, requests, nil)) == 2) && (Znth(0, Znth(i, requests, nil), 0) == 1) && (1 <= Znth(1, Znth(i, requests, nil), 0) && Znth(1, Znth(i, requests, nil), 0) <= n)))) &&
      q == Zlength(requests) &&
      Zlength(froms) == n - 1 && Zlength(tos) == n - 1 &&
      Zlength(xlo) == q && Zlength(xhi) == q && Zlength(query_mem) == 6 * q &&
      (forall i, (0 <= i && i < n - 1) =>
        (fst(edges[i]) == froms[i] + 1 &&
         snd(edges[i]) == tos[i] + 1)) &&
      (forall i, (0 <= i && i < q) =>
        (query_mem[6 * i + 1] == Some(Znth(1, requests[i], 0) - 1) &&
         query_mem[6 * i + 4] == Some(xlo[i]) &&
         query_mem[6 * i + 5] == Some(xhi[i]) &&
         ((Zlength(requests[i]) == 4 &&
           query_mem[6 * i] == Some(2) &&
           query_mem[6 * i + 2] == Some(Znth(3, requests[i], 0)) &&
           merge_int64_by_ints(xlo[i], xhi[i], Znth(2, requests[i], 0))) ||
          (Zlength(requests[i]) == 2 &&
           query_mem[6 * i] == Some(1) &&
           query_mem[6 * i + 2] == Some(0) &&
           merge_int64_by_ints(xlo[i], xhi[i], 0))))) &&
      IntArray::full(eu, n - 1, froms) *
      IntArray::full(ev, n - 1, tos) *
      IntArray::mixed_full(queries, 6 * q, query_mem) *
      Int64Array::undef_full(out, q)
    Ensure
      exists result,
        Spec(n, edges, requests, result) && __return == Zlength(result) &&
        IntArray::full(eu, n - 1, froms) * IntArray::full(ev, n - 1, tos) *
        IntArray::mixed_full(queries, 6 * q, query_mem) *
        Int64Array::full(out, __return, result) * Int64Array::undef_seg(out, __return, q)
*/
/* QCP_INSERT_END:P072_276E_little_girl_and_problem_on_trees.contract */
{
    total_nodes = n + 2;
    root_value = 0;
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
    int *branch = malloc((size_t)n * sizeof(*branch)), *depth = malloc((size_t)n * sizeof(*depth)),
        *flat = malloc((size_t)n * sizeof(*flat)), *base = malloc((size_t)n * sizeof(*base)),
        *blen = calloc((size_t)n, sizeof(*blen));
    branch[0] = -1;
    depth[0] = 0;
    flat[0] = 0;
    int bc = 0, cursor = 1;
    for (int e = head[0]; e != -1; e = nxt[e])
    {
        int v = to[e], p = 0;
        int b = bc++;
        base[b] = cursor;
        int d = 1;
        while (1)
        {
            branch[v] = b;
            depth[v] = d;
            flat[v] = cursor++;
            blen[b] = d;
            int nv = -1;
            for (int z = head[v]; z != -1; z = nxt[z])
                if (to[z] != p)
                {
                    nv = to[z];
                    break;
                }
            if (nv < 0)
                break;
            p = v;
            v = nv;
            ++d;
        }
    }
    branch_bit = calloc((size_t)n + 5, sizeof(*branch_bit));
    depth_bit = calloc((size_t)n + 5, sizeof(*depth_bit));
    int answers = 0;
    for (int i = 0; i < q; ++i)
    {
        int type = queries[i].type, v = queries[i].v;
        if (type == 1)
        {
            out[answers++] =
                v == 0 ? root_value : get(branch_bit, flat[v]) + get(depth_bit, depth[v]);
        }
        else
        {
            long long x = queries[i].x;
            int d = queries[i].d;
            if (v == 0)
            {
                root_value += x;
                range_add(depth_bit, 1, d, x);
                continue;
            }
            int b = branch[v], h = depth[v], lo = h - d;
            if (lo < 1)
                lo = 1;
            int hi = h + d;
            if (hi > blen[b])
                hi = blen[b];
            range_add(branch_bit, base[b] + lo - 1, base[b] + hi - 1, x);
            if (d >= h)
            {
                root_value += x;
                int reach = d - h;
                range_add(depth_bit, 1, reach, x);
                range_add(branch_bit, base[b], base[b] + (reach < blen[b] ? reach : blen[b]) - 1,
                          -x);
            }
        }
    }
    free(head);
    free(to);
    free(nxt);
    free(branch);
    free(depth);
    free(flat);
    free(base);
    free(blen);
    free(branch_bit);
    free(depth_bit);
    branch_bit = depth_bit = NULL;
    return answers;
}
// int main(void)
// {
//     int n, q;
//     if (scanf("%d %d", &n, &q) != 2)
//         return 0;
//     int *eu = malloc((size_t)(n - 1) * sizeof(*eu)), *ev = malloc((size_t)(n - 1) * sizeof(*ev));
//     for (int i = 0; i < n - 1; ++i)
//     {
//         scanf("%d %d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     Query *queries = malloc((size_t)q * sizeof(*queries));
//     for (int i = 0; i < q; ++i)
//     {
//         scanf("%d %d", &queries[i].type, &queries[i].v);
//         --queries[i].v;
//         queries[i].x = 0;
//         queries[i].d = 0;
//         if (queries[i].type != 1)
//             scanf("%lld %d", &queries[i].x, &queries[i].d);
//     }
//     long long *out = malloc((size_t)q * sizeof(*out));
//     int answers = solver(n, eu, ev, q, queries, out);
//     for (int i = 0; i < answers; ++i)
//         printf("%lld\n", out[i]);
//     free(eu);
//     free(ev);
//     free(queries);
//     free(out);
//     return 0;
// }
