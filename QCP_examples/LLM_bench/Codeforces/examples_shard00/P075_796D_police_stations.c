/* Codeforces 796/D - Police Stations */
// #include <stdio.h>
// #include <stdlib.h>
typedef struct
{
    int to, next, id;
} Edge;
/* QCP_INSERT_BEGIN:P075_796D_police_stations.support */
/*@ Extern Coq
      (Pre : Z -> Z -> list Z -> list (Z * Z) -> Prop)
      (Spec : Z -> Z -> list Z -> list (Z * Z) -> list Z -> Prop)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P075_796D_police_stations_lib */
/* QCP_INSERT_END:P075_796D_police_stations.support */
static int solver(int n, int k, int d, const int *stations, const int *eu, const int *ev,
                  int *out) /* QCP_INSERT_BEGIN:P075_796D_police_stations.contract */

/*@ With (stations_data : list Z)
             (edges : list (Z * Z))
             (eu_data ev_data : list Z)
    Require
      2 <= n && n <= 300000 &&
      0 <= d && d < n &&
      1 <= Zlength(stations_data) && Zlength(stations_data) <= 300000 &&
      Zlength(edges) == n-1 &&
      (forall i, (0 <= i && i < Zlength(stations_data)) => (1 <= stations_data[i] && stations_data[i] <= n)) &&
      Pre(n, d, stations_data, edges) &&
      k == Zlength(stations_data) &&
      Zlength(eu_data) == Zlength(edges) && Zlength(ev_data) == Zlength(edges) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (eu_data[i] == fst(edges[i]) && ev_data[i] == snd(edges[i]))) &&
      IntArray::full(stations, k, stations_data) *
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      IntArray::undef_full(out, Zlength(edges))
    Ensure
      exists removed,
        Spec(n, d, stations_data, edges, removed) && __return == Zlength(removed) &&
        IntArray::full(stations, k, stations_data) *
        IntArray::full(eu, Zlength(edges), eu_data) *
        IntArray::full(ev, Zlength(edges), ev_data) *
        IntArray::full(out, Zlength(removed), removed) *
        IntArray::undef_seg(out, Zlength(removed), Zlength(edges))
*/
/* QCP_INSERT_END:P075_796D_police_stations.contract */
{
    int *head = malloc((size_t)n * sizeof(*head)), *dist = malloc((size_t)n * sizeof(*dist)),
        *q = malloc((size_t)n * sizeof(*q));
    for (int i = 0; i < n; ++i)
    {
        head[i] = -1;
        dist[i] = -1;
    }
    int l = 0, r = 0;
    for (int i = 0; i < k; ++i)
    {
        int p = stations[i];
        if (dist[p] < 0)
        {
            dist[p] = 0;
            q[r++] = p;
        }
    }
    Edge *e = malloc((size_t)(2 * n - 2) * sizeof(*e));
    int ec = 0;
    for (int i = 1; i < n; ++i)
    {
        int u = eu[i - 1], v = ev[i - 1];
        e[ec] = (Edge){v, head[u], i};
        head[u] = ec++;
        e[ec] = (Edge){u, head[v], i};
        head[v] = ec++;
    }
    unsigned char *keep = calloc((size_t)n, 1);
    while (l < r)
    {
        int v = q[l++];
        if (dist[v] == d)
            continue;
        for (int z = head[v]; z != -1; z = e[z].next)
            if (dist[e[z].to] < 0)
            {
                dist[e[z].to] = dist[v] + 1;
                keep[e[z].id] = 1;
                q[r++] = e[z].to;
            }
    }
    int count = 0;
    for (int i = 1; i < n; ++i)
        if (!keep[i])
            out[count++] = i;
    free(head);
    free(dist);
    free(q);
    free(e);
    free(keep);
    return count;
}
// int main(void)
// {
//     int n, k, d;
//     if (scanf("%d %d %d", &n, &k, &d) != 3)
//         return 0;
//     int *stations = malloc((size_t)k * sizeof(*stations)),
//         *eu = malloc((size_t)(n - 1) * sizeof(*eu)), *ev = malloc((size_t)(n - 1) * sizeof(*ev)),
//         *out = malloc((size_t)(n - 1) * sizeof(*out));
//     for (int i = 0; i < k; ++i)
//     {
//         scanf("%d", &stations[i]);
//         --stations[i];
//     }
//     for (int i = 0; i < n - 1; ++i)
//     {
//         scanf("%d %d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     int count = solver(n, k, d, stations, eu, ev, out);
//     printf("%d\n", count);
//     for (int i = 0; i < count; ++i)
//         printf("%d ", out[i]);
//     putchar('\n');
//     free(stations);
//     free(eu);
//     free(ev);
//     free(out);
//     return 0;
// }
