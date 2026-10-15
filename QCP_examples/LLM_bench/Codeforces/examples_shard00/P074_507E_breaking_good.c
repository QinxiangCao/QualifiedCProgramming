/* Codeforces 507/E - Breaking Good */
// #include <stdio.h>
// #include <stdlib.h>
typedef struct
{
    int u, v, z;
} InputEdge;
typedef struct
{
    int to, next, id;
} Adj;
/* QCP_INSERT_BEGIN:P074_507E_breaking_good.support */
/*@ Extern Coq
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (Pre : Z -> list (Z * Z * Z) -> Prop)
      (Spec : Z -> list (Z * Z * Z) -> list (Z * Z * Z) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P074_507E_breaking_good_lib */
/* QCP_INSERT_END:P074_507E_breaking_good.support */
static int solver(int n, int m, const InputEdge *input,
                  InputEdge *out) /* QCP_INSERT_BEGIN:P074_507E_breaking_good.contract */

/*@ With (roads : list (Z * Z * Z))
             (raw_input : list Z)
    Require
      2 <= n && n <= 100000 &&
      Zlength(roads) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(roads)) => ((1 <= ztriple_1(roads[i]) && ztriple_1(roads[i]) <= n) && (1 <= ztriple_2(roads[i]) && ztriple_2(roads[i]) <= n) && (ztriple_1(roads[i]) != ztriple_2(roads[i])) && ((ztriple_3(roads[i])==0) || (ztriple_3(roads[i])==1)))) &&
      Pre(n, roads) &&
      m == Zlength(roads) && Zlength(raw_input) == 3 * m &&
      (forall i, (0 <= i && i < m) =>
        (raw_input[3 * i] == ztriple_1(roads[i]) - 1 &&
         raw_input[3 * i + 1] == ztriple_2(roads[i]) - 1 &&
         raw_input[3 * i + 2] == ztriple_3(roads[i]))) &&
      IntArray::full(input, 3 * m, raw_input) *
      IntArray::undef_full(out, 3 * m)
    Ensure
      exists changes raw_output,
        Spec(n, roads, changes) && __return == Zlength(changes) &&
        (forall i, (0 <= i && i < __return) =>
          (raw_output[3 * i] == ztriple_1(changes[i]) - 1 &&
           raw_output[3 * i + 1] == ztriple_2(changes[i]) - 1 &&
           raw_output[3 * i + 2] == ztriple_3(changes[i]))) &&
        IntArray::full(input, 3 * m, raw_input) *
        IntArray::full(out, 3 * __return, raw_output) *
        IntArray::undef_seg(out, 3 * __return, 3 * m)
*/
/* QCP_INSERT_END:P074_507E_breaking_good.contract */
{
    InputEdge *e = malloc((size_t)m * sizeof(*e));
    Adj *ad = malloc((size_t)2 * m * sizeof(*ad));
    int *head = malloc((size_t)n * sizeof(*head));
    for (int i = 0; i < n; ++i)
        head[i] = -1;
    int ec = 0;
    for (int i = 0; i < m; ++i)
    {
        e[i] = input[i];
        ad[ec] = (Adj){e[i].v, head[e[i].u], i};
        head[e[i].u] = ec++;
        ad[ec] = (Adj){e[i].u, head[e[i].v], i};
        head[e[i].v] = ec++;
    }
    int *dist = malloc((size_t)n * sizeof(*dist)), *ones = malloc((size_t)n * sizeof(*ones)),
        *par = malloc((size_t)n * sizeof(*par)), *q = malloc((size_t)n * sizeof(*q));
    for (int i = 0; i < n; ++i)
    {
        dist[i] = -1;
        ones[i] = -1;
        par[i] = -1;
    }
    int l = 0, r = 0;
    q[r++] = 0;
    dist[0] = 0;
    ones[0] = 0;
    while (l < r)
    {
        int v = q[l++];
        for (int z = head[v]; z != -1; z = ad[z].next)
        {
            int u = ad[z].to, id = ad[z].id;
            if (dist[u] < 0)
            {
                dist[u] = dist[v] + 1;
                ones[u] = ones[v] + e[id].z;
                par[u] = id;
                q[r++] = u;
            }
            else if (dist[u] == dist[v] + 1 && ones[v] + e[id].z > ones[u])
            {
                ones[u] = ones[v] + e[id].z;
                par[u] = id;
            }
        }
    }
    unsigned char *path = calloc((size_t)m, 1);
    int v = n - 1;
    while (v != 0 && par[v] >= 0)
    {
        int id = par[v];
        path[id] = 1;
        v = e[id].u == v ? e[id].v : e[id].u;
    }
    int changes = 0;
    for (int i = 0; i < m; ++i)
    {
        if (path[i] && !e[i].z)
            out[changes++] = (InputEdge){e[i].u, e[i].v, 1};
        else if (!path[i] && e[i].z)
            out[changes++] = (InputEdge){e[i].u, e[i].v, 0};
    }
    free(e);
    free(ad);
    free(head);
    free(dist);
    free(ones);
    free(par);
    free(q);
    free(path);
    return changes;
}
// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     InputEdge *e = malloc((size_t)m * sizeof(*e)), *out = malloc((size_t)m * sizeof(*out));
//     for (int i = 0; i < m; ++i)
//     {
//         scanf("%d %d %d", &e[i].u, &e[i].v, &e[i].z);
//         --e[i].u;
//         --e[i].v;
//     }
//     int changes = solver(n, m, e, out);
//     printf("%d\n", changes);
//     for (int i = 0; i < changes; ++i)
//         printf("%d %d %d\n", out[i].u + 1, out[i].v + 1, out[i].z);
//     free(e);
//     free(out);
//     return 0;
// }
