/* Codeforces 1067/B - Multihedgehog */
// #include <stdio.h>
// #include <stdlib.h>

static int n, *head, *to, *nxt, *deg;

/* QCP_INSERT_BEGIN:P057_1067B_multihedgehog.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : Z -> Z -> list (Z * Z) -> Prop)
      (GraphPre : Z -> list (Z * Z) -> Prop)
      (Spec : Z -> Z -> list (Z * Z) -> Z -> Prop)
      (CurrentEdgeFresh : list (Z * Z) -> Z -> Prop)
      (AdjacencyBuildState : Z -> list (Z * Z) -> Z ->
        list Z -> list Z -> list Z -> Prop)
      (AdjacencyModel : Z -> list (Z * Z) ->
        list Z -> list Z -> list Z -> Prop)
      (DegreePrefix : Z -> list (Z * Z) -> Z -> list Z -> Prop)
      (BFSResult : Z -> list (Z * Z) -> Z ->
        list Z -> list Z -> Z -> Prop)
      (BFSData : Z -> list (Z * Z) -> Z -> list Z -> list Z -> Prop)
      (BFSQueueState : Z -> list (Z * Z) -> Z -> Z -> Z ->
        list Z -> list Z -> list Z -> Prop)
      (BFSAdjState : Z -> list (Z * Z) -> Z -> Z -> Z ->
        list Z -> list Z -> list Z -> list Z -> list Z -> list Z ->
        Z -> Z -> Prop)
      (AncestorAfter : list Z -> Z -> Z -> Z -> Prop)
      (DecisionPrefix : Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (DiameterDecision : Z -> list Z -> Z -> Z -> Prop)
      (SolverDecision : Z -> Z -> list (Z * Z) ->
        list Z -> list Z -> Z -> Z -> list Z -> list Z -> list Z ->
        Z -> Z -> Prop)
      (SolverCertificate : Z -> Z -> list (Z * Z) ->
        list Z -> list Z -> Z -> list Z -> list Z -> Z -> Z ->
        list Z -> list Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::full_shape : Z -> Z -> Assertion)
      (IntArray::seg_shape : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P057_1067B_multihedgehog_lib */
/* QCP_INSERT_END:P057_1067B_multihedgehog.support */

void *malloc(unsigned long size)
    /*@ malloc_int
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
    /*@ malloc_shape
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::full_shape(__return, cap)
*/
    ;

void *calloc(unsigned long nmemb, unsigned long size)
    /*@ calloc_int
    With (cap : Z)
    Require 0 <= cap && nmemb == cap && size == sizeof(int)
    Ensure __return != 0 &&
      IntArray::full(__return, cap, repeat_Z(0, cap))
*/
    ;

void free(void *ptr)
    /*@ free_int
    With (cap : Z)
    Require
      0 <= cap && exists values,
        Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
    ;

static int bfs(int src, int *parent, int *dist)
/*@ bfs_run
    With (nv : Z) (edges : list (Z * Z))
             (head_p to_p next_p : Z)
             (head_data to_data next_data : list Z)
    Require
      1 <= nv && nv <= 100000 && 0 <= src && src < nv &&
      GraphPre(nv, edges) &&
      AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
      store(&n, int, nv) *
      store(&head, int *, head_p) * store(&to, int *, to_p) *
      store(&nxt, int *, next_p) *
      IntArray::full(head_p, nv, head_data) *
      IntArray::full(to_p, 2 * nv - 2, to_data) *
      IntArray::full(next_p, 2 * nv - 2, next_data) *
      IntArray::full_shape(parent, nv) * IntArray::full_shape(dist, nv)
    Ensure
      exists parent_data dist_data,
        BFSResult(nv, edges, src, parent_data, dist_data, __return) &&
        store(&n, int, nv) *
        store(&head, int *, head_p) * store(&to, int *, to_p) *
        store(&nxt, int *, next_p) *
        IntArray::full(head_p, nv, head_data) *
        IntArray::full(to_p, 2 * nv - 2, to_data) *
        IntArray::full(next_p, 2 * nv - 2, next_data) *
        IntArray::full(parent, nv, parent_data) *
        IntArray::full(dist, nv, dist_data)
*/
{
    int *q = malloc(n * sizeof(*q))
        /*@ where (malloc_int) cap = n */;
    int l = 0, r = 0;
    q[r] = src;
    ++r;

    /*@ Inv Assert
          exists parent_data dist_data,
          parent == parent@pre && dist == dist@pre && src == src@pre &&
          1 <= nv && nv <= 100000 && 0 <= src@pre && src@pre < nv &&
          GraphPre(nv, edges) &&
          AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
          l == 0 && r == 1 && 0 <= i && i <= nv &&
          Zlength(parent_data) == nv && Zlength(dist_data) == nv &&
          (forall j, (0 <= j && j < i) => parent_data[j] == -1) &&
          (forall j, (0 <= j && j < i) => dist_data[j] == -1) &&
          store(&n, int, nv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&nxt, int *, next_p) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data) *
          IntArray::seg(q, 0, 1, cons(src@pre, nil)) *
          IntArray::undef_seg(q, 1, nv) *
          IntArray::full(parent@pre, nv, parent_data) *
          IntArray::full(dist@pre, nv, dist_data)
    */
    for (int i = 0; i < n; ++i)
    {
        dist[i] = -1;
        parent[i] = -1;
    }

    dist[src] = 0;
    int far = src;

    /*@ Inv Assert
          exists queue_data parent_data dist_data,
            parent == parent@pre && dist == dist@pre && src == src@pre &&
            1 <= nv && nv <= 100000 &&
            GraphPre(nv, edges) &&
            AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
            0 <= l && l <= r && r == Zlength(queue_data) && r <= nv &&
            0 <= far && far < nv &&
            (forall qindex, (0 <= qindex && qindex < r) =>
              (0 <= queue_data[qindex] && queue_data[qindex] < nv)) &&
            BFSQueueState(nv, edges, src@pre, l, far,
                          queue_data, parent_data, dist_data) &&
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::seg(q, 0, r, queue_data) *
            IntArray::undef_seg(q, r, nv) *
            IntArray::full(parent@pre, nv, parent_data) *
            IntArray::full(dist@pre, nv, dist_data)
    */
    while (l < r)
    {
        int v = q[l];
        ++l;
        if (dist[v] > dist[far])
            far = v;

        /*@ Inv Assert
              exists queue_data parent_data dist_data,
                parent == parent@pre && dist == dist@pre && src == src@pre &&
                1 <= nv && nv <= 100000 &&
                GraphPre(nv, edges) &&
                AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
                0 < l && l <= r && r == Zlength(queue_data) && r <= nv &&
                0 <= v && v < nv && 0 <= far && far < nv &&
                -1 <= e && e < 2 * nv - 2 &&
                (e != -1 =>
                  (0 <= to_data[e] && to_data[e] < nv &&
                   -1 <= next_data[e] && next_data[e] < 2 * nv - 2)) &&
                ((e != -1 && dist_data[to_data[e]] < 0) => r < nv) &&
                BFSAdjState(nv, edges, src@pre, l, far,
                            queue_data, parent_data, dist_data,
                            head_data, to_data, next_data, v, e) &&
                store(&n, int, nv) *
                store(&head, int *, head_p) * store(&to, int *, to_p) *
                store(&nxt, int *, next_p) *
                IntArray::full(head_p, nv, head_data) *
                IntArray::full(to_p, 2 * nv - 2, to_data) *
                IntArray::full(next_p, 2 * nv - 2, next_data) *
                IntArray::seg(q, 0, r, queue_data) *
                IntArray::undef_seg(q, r, nv) *
                IntArray::full(parent@pre, nv, parent_data) *
                IntArray::full(dist@pre, nv, dist_data)
        */
        for (int e = head[v]; e != -1; e = nxt[e])
        {
            if (dist[to[e]] < 0)
            {
                dist[to[e]] = dist[v] + 1;
                parent[to[e]] = v;
                q[r] = to[e];
                ++r;
            }
        }
    }

    /*@ Assert
          exists queue_data parent_data dist_data,
            parent == parent@pre && dist == dist@pre && src == src@pre &&
            1 <= nv && l == nv && r == nv && Zlength(queue_data) == nv &&
            BFSResult(nv, edges, src@pre, parent_data, dist_data, far) &&
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::full(q, nv, queue_data) *
            IntArray::full(parent@pre, nv, parent_data) *
            IntArray::full(dist@pre, nv, dist_data)
    */
    free(q) /*@ where (free_int) cap = nv */;
    return far;
}

static int solver(int nn, long long k, const int *eu, const int *ev)
/* QCP_INSERT_BEGIN:P057_1067B_multihedgehog.contract */
/*@ With (nv : Z) (edges : list (Z * Z))
             (eu_data ev_data : list Z)
             (n_before head_before to_before next_before deg_before : Z)
    Require
      1 <= nv && nv <= 100000 &&
      1 <= k && k <= 1000000000 &&
      Zlength(edges) == nv - 1 &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (1 <= fst(edges[i]) && fst(edges[i]) <= nv &&
         1 <= snd(edges[i]) && snd(edges[i]) <= nv)) &&
      Pre(nv, k, edges) &&
      nn == nv && Zlength(eu_data) == Zlength(edges) &&
      Zlength(ev_data) == Zlength(edges) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (eu_data[i] == fst(edges[i]) - 1 &&
         ev_data[i] == snd(edges[i]) - 1)) &&
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      store(&n, int, n_before) *
      store(&head, int *, head_before) * store(&to, int *, to_before) *
      store(&nxt, int *, next_before) * store(&deg, int *, deg_before)
    Ensure
      exists head_after to_after next_after deg_after,
        Spec(nv, k, edges, __return) &&
        IntArray::full(eu, Zlength(edges), eu_data) *
        IntArray::full(ev, Zlength(edges), ev_data) *
        store(&n, int, nv) *
        store(&head, int *, head_after) * store(&to, int *, to_after) *
        store(&nxt, int *, next_after) * store(&deg, int *, deg_after)
*/
/* QCP_INSERT_END:P057_1067B_multihedgehog.contract */
{
    n = nn;
    head = malloc(n * sizeof(*head))
        /*@ where (malloc_int) cap = nv */;
    deg = calloc(n, sizeof(*deg))
        /*@ where (calloc_int) cap = nv */;
    to = malloc((2 * n - 2) * sizeof(*to))
        /*@ where (malloc_int) cap = 2 * nv - 2 */;
    nxt = malloc((2 * n - 2) * sizeof(*nxt))
        /*@ where (malloc_int) cap = 2 * nv - 2 */;

    /*@ Inv Assert
          exists head_p to_p next_p deg_p head_init,
            nn == nv && eu == eu@pre && ev == ev@pre &&
            k == k@pre && 1 <= nv && nv <= 100000 &&
            1 <= k && k <= 1000000000 &&
            Pre(nv, k, edges) && GraphPre(nv, edges) &&
            0 <= i && i <= nv && Zlength(head_init) == i &&
            (forall q, (0 <= q && q < i) => head_init[q] == -1) &&
            (forall j, (0 <= j && j < nv - 1) =>
              (0 <= eu_data[j] && eu_data[j] < nv &&
               0 <= ev_data[j] && ev_data[j] < nv &&
               eu_data[j] == fst(edges[j]) - 1 &&
               ev_data[j] == snd(edges[j]) - 1)) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::seg(head_p, 0, i, head_init) *
            IntArray::undef_seg(head_p, i, nv) *
            IntArray::undef_full(to_p, 2 * nv - 2) *
            IntArray::undef_full(next_p, 2 * nv - 2) *
            IntArray::full(deg_p, nv, repeat_Z(0, nv))
    */
    for (int i = 0; i < n; ++i)
        head[i] = -1;

    int ec = 0;
    /*@ Inv Assert
          exists head_p to_p next_p deg_p,
          exists head_data to_done next_done degree_data,
            nn == nv && eu == eu@pre && ev == ev@pre &&
            k == k@pre && 1 <= nv && nv <= 100000 &&
            1 <= k && k <= 1000000000 &&
            Pre(nv, k, edges) &&
            0 <= i && i <= nv - 1 && ec == 2 * i &&
            Zlength(head_data) == nv &&
            Zlength(to_done) == ec && Zlength(next_done) == ec &&
            Zlength(degree_data) == nv &&
            AdjacencyBuildState(nv, edges, i,
                                head_data, to_done, next_done) &&
            DegreePrefix(nv, edges, i, degree_data) &&
            (forall index, CurrentEdgeFresh(edges, index)) &&
            (forall j, (0 <= j && j < nv - 1) =>
              (0 <= eu_data[j] && eu_data[j] < nv &&
               0 <= ev_data[j] && ev_data[j] < nv &&
               eu_data[j] == fst(edges[j]) - 1 &&
               ev_data[j] == snd(edges[j]) - 1)) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::seg(to_p, 0, ec, to_done) *
            IntArray::undef_seg(to_p, ec, 2 * nv - 2) *
            IntArray::seg(next_p, 0, ec, next_done) *
            IntArray::undef_seg(next_p, ec, 2 * nv - 2) *
            IntArray::full(deg_p, nv, degree_data)
    */
    for (int i = 0; i + 1 < n; ++i)
    {
        int u = eu[i], v = ev[i];
        to[ec] = v;
        nxt[ec] = head[u];
        head[u] = ec;
        ++ec;
        to[ec] = u;
        nxt[ec] = head[v];
        head[v] = ec;
        ++ec;
        ++deg[u];
        ++deg[v];
    }

    /*@ Assert
          exists head_p to_p next_p deg_p,
          exists head_data to_data next_data degree_data,
            nn == nv && eu == eu@pre && ev == ev@pre &&
            k == k@pre && ec == 2 * nv - 2 &&
            1 <= nv && nv <= 100000 && 1 <= k && k <= 1000000000 &&
            Pre(nv, k, edges) && GraphPre(nv, edges) &&
            AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
            DegreePrefix(nv, edges, nv - 1, degree_data) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::full(deg_p, nv, degree_data)
    */
    int *p = malloc(n * sizeof(*p))
        /*@ where (malloc_shape) cap = nv */;
    int *d = malloc(n * sizeof(*d))
        /*@ where (malloc_shape) cap = nv */;
    int ok = 1;

    int a = bfs(0, p, d)
        /*@ where (bfs_run) nv = nv, edges = edges */;

    /*@ Assert
          exists first_parent first_dist,
          exists head_p to_p next_p deg_p,
          exists head_data to_data next_data degree_data,
            BFSResult(nv, edges, 0, first_parent, first_dist, a) &&
            nn == nv && eu == eu@pre && ev == ev@pre &&
            k == k@pre && ok == 1 && ec == 2 * nv - 2 &&
            1 <= nv && nv <= 100000 &&
            1 <= k && k <= 1000000000 &&
            GraphPre(nv, edges) &&
            AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
            DegreePrefix(nv, edges, nv - 1, degree_data) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::full(deg_p, nv, degree_data) *
            IntArray::full_shape(p, nv) *
            IntArray::full_shape(d, nv)
    */
    int b = bfs(a, p, d)
        /*@ where (bfs_run) nv = nv, edges = edges */;

    /*@ Assert
          exists first_parent first_dist second_parent second_dist,
          exists head_p to_p next_p deg_p,
          exists head_data to_data next_data degree_data,
            BFSResult(nv, edges, 0, first_parent, first_dist, a) &&
            BFSResult(nv, edges, a, second_parent, second_dist, b) &&
            0 <= a && a < nv && 0 <= b && b < nv &&
            nn == nv && eu == eu@pre && ev == ev@pre &&
            k == k@pre && ok == 1 && ec == 2 * nv - 2 &&
            1 <= nv && nv <= 100000 &&
            1 <= k && k <= 1000000000 &&
            GraphPre(nv, edges) &&
            AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
            DegreePrefix(nv, edges, nv - 1, degree_data) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::full(deg_p, nv, degree_data) *
            IntArray::full(p, nv, second_parent) *
            IntArray::full(d, nv, second_dist)
    */
    if (d[b] != 2 * k)
        ok = 0;

    int center = b;
    /*@ Inv Assert
          exists first_parent first_dist second_parent second_dist,
          exists head_p to_p next_p deg_p,
          exists head_data to_data next_data degree_data,
            BFSResult(nv, edges, 0, first_parent, first_dist, a) &&
            BFSResult(nv, edges, a, second_parent, second_dist, b) &&
            GraphPre(nv, edges) &&
            AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
            DegreePrefix(nv, edges, nv - 1, degree_data) &&
            nn == nv && eu == eu@pre && ev == ev@pre && k == k@pre &&
            ec == 2 * nv - 2 &&
            1 <= nv && nv <= 100000 &&
            1 <= k && k <= 1000000000 &&
            DiameterDecision(k, second_dist, b, ok) &&
            0 <= i && i <= k &&
            0 <= center && center < nv &&
            AncestorAfter(second_parent, b, i, center) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::full(deg_p, nv, degree_data) *
            IntArray::full(p, nv, second_parent) *
            IntArray::full(d, nv, second_dist)
    */
    for (long long i = 0; ok && i < k; ++i)
        center = p[center];

    if (ok)
    {
        /*@ Assert
              exists first_parent first_dist second_parent second_dist,
              exists head_p to_p next_p deg_p,
              exists head_data to_data next_data degree_data,
                BFSResult(nv, edges, 0, first_parent, first_dist, a) &&
                BFSResult(nv, edges, a, second_parent, second_dist, b) &&
                GraphPre(nv, edges) &&
                AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
                DegreePrefix(nv, edges, nv - 1, degree_data) &&
                nn == nv && eu == eu@pre && ev == ev@pre &&
                k == k@pre && ok == 1 &&
                1 <= nv && nv <= 100000 &&
                1 <= k && k <= 1000000000 &&
                ec == 2 * nv - 2 && 0 <= center && center < nv &&
                AncestorAfter(second_parent, b, k, center) &&
                second_dist[b] == 2 * k &&
                IntArray::full(eu, nv - 1, eu_data) *
                IntArray::full(ev, nv - 1, ev_data) *
                store(&n, int, nv) *
                store(&head, int *, head_p) * store(&to, int *, to_p) *
                store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
                IntArray::full(head_p, nv, head_data) *
                IntArray::full(to_p, 2 * nv - 2, to_data) *
                IntArray::full(next_p, 2 * nv - 2, next_data) *
                IntArray::full(deg_p, nv, degree_data) *
                IntArray::full_shape(p, nv) *
                IntArray::full_shape(d, nv)
        */
        bfs(center, p, d)
            /*@ where (bfs_run) nv = nv, edges = edges */;
    }

    /*@ Inv Assert
          exists first_parent first_dist second_parent second_dist,
          exists center_parent center_dist,
          exists head_p to_p next_p deg_p,
          exists head_data to_data next_data degree_data,
            BFSResult(nv, edges, 0, first_parent, first_dist, a) &&
            BFSResult(nv, edges, a, second_parent, second_dist, b) &&
            nn == nv && eu == eu@pre && ev == ev@pre &&
            k == k@pre && GraphPre(nv, edges) &&
            1 <= k && k <= 1000000000 &&
            AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
            DegreePrefix(nv, edges, nv - 1, degree_data) &&
            ec == 2 * nv - 2 && 0 <= v && v <= nv &&
            SolverDecision(nv, k, edges, second_parent, second_dist,
                           b, center, center_parent, center_dist,
                           degree_data, v, ok) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::full(deg_p, nv, degree_data) *
            IntArray::full(p, nv, center_parent) *
            IntArray::full(d, nv, center_dist)
    */
    for (int v = 0; ok && v < n; ++v)
    {
        if (d[v] > k || (d[v] == k && deg[v] != 1) ||
            (d[v] < k && ((v == center && deg[v] < 3) || (v != center && deg[v] < 4))))
            ok = 0;
    }

    /*@ Assert
          exists first_parent first_dist second_parent second_dist,
          exists center_parent center_dist,
          exists head_p to_p next_p deg_p,
          exists head_data to_data next_data degree_data,
            nn == nv && eu == eu@pre && ev == ev@pre &&
            k == k@pre && 1 <= k && k <= 1000000000 &&
            ec == 2 * nv - 2 && GraphPre(nv, edges) &&
            SolverCertificate(nv, k, edges,
                              first_parent, first_dist, a,
                              second_parent, second_dist, b, center,
                              center_parent, center_dist, degree_data, ok) &&
            Spec(nv, k, edges, ok) &&
            AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
            IntArray::full(eu, nv - 1, eu_data) *
            IntArray::full(ev, nv - 1, ev_data) *
            store(&n, int, nv) *
            store(&head, int *, head_p) * store(&to, int *, to_p) *
            store(&nxt, int *, next_p) * store(&deg, int *, deg_p) *
            IntArray::full(head_p, nv, head_data) *
            IntArray::full(to_p, 2 * nv - 2, to_data) *
            IntArray::full(next_p, 2 * nv - 2, next_data) *
            IntArray::full(deg_p, nv, degree_data) *
            IntArray::full(p, nv, center_parent) *
            IntArray::full(d, nv, center_dist)
    */

    free(head) /*@ where (free_int) cap = nv */;
    free(to) /*@ where (free_int) cap = 2 * nv - 2 */;
    free(nxt) /*@ where (free_int) cap = 2 * nv - 2 */;
    free(deg) /*@ where (free_int) cap = nv */;
    free(p) /*@ where (free_int) cap = nv */;
    free(d) /*@ where (free_int) cap = nv */;
    return ok;
}

// int main(void)
// {
//     long long k;
//     if (scanf("%d %lld", &n, &k) != 2)
//         return 0;
//     int *eu = malloc((size_t)(n - 1) * sizeof(int)), *ev = malloc((size_t)(n - 1) * sizeof(int));
//     for (int i = 0; i < n - 1; ++i)
//     {
//         scanf("%d%d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     puts(solver(n, k, eu, ev) ? "Yes" : "No");
//     free(eu);
//     free(ev);
//     return 0;
// }
