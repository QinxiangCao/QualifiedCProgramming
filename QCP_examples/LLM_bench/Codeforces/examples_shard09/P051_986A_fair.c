/*
 * Codeforces 986/A - Fair  (rating 1600, BFS)
 *
 * Roads are unweighted, so one multi-source BFS per goods type gives, for every
 * town, the distance to the nearest town producing that type (k <= 100 BFS
 * runs).  Each town then sums the s smallest of its k distances.
 *
 * solver() takes the raw town types and road list, so the graph and every BFS
 * happen inside it; main() only reads and prints.
 */

// #include <stdio.h>
// #include <stdlib.h>
#include "array2_ext_def.h"
/* QCP_INSERT_BEGIN:shard09-P051-solver-support */
/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P051_986A_fair_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Pre : Z -> Z -> list (Z * Z) -> list Z -> Prop)
      (Spec : Z -> Z -> list (Z * Z) -> list Z -> list Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P051-solver-support */

/*@ Extern Coq
      (ZSum : list Z -> Z)
      (MReach : Z -> list (Z * Z) -> list Z -> Z -> Z -> Z -> Prop)
      (BfsDist : Z -> list (Z * Z) -> list Z -> Z -> Z -> Z -> Prop)
      (AdjBuild : Z -> Z -> list (Z * Z) -> list Z -> list Z -> list Z -> Prop)
      (NxtRange : Z -> list Z -> Prop)
      (ArcToRange : Z -> Z -> list Z -> Prop)
      (BfsRowResult : Z -> list (Z * Z) -> list Z -> Z -> list Z -> Prop)
      (BfsInit : Z -> list Z -> Z -> list Z -> list Z -> Z -> Prop)
      (BfsCore : Z -> list (Z * Z) -> list Z -> Z -> list Z -> list Z -> Prop)
      (BfsExpanded : Z -> list (Z * Z) -> list Z -> list Z -> Z -> Prop)
      (BfsBounded : list Z -> list Z -> Z -> Prop)
      (BfsScan : Z -> list (Z * Z) -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (BfsRows : Z -> list (Z * Z) -> list Z -> list (list Z) -> Z -> Prop)
      (TmpPrefix : Z -> list (Z * Z) -> list Z -> Z -> list Z -> Z -> Prop)
      (OutPrefix : Z -> Z -> list (Z * Z) -> list Z -> list Z -> Z -> Prop)
*/


#define MAXN 100005
#define MAXM 100005
#define MAXK 105

/* file-scope work arrays, rebuilt on every call */
static int head_[MAXN], nxt_[2 * MAXM], to_[2 * MAXM];
static int queue_[MAXN];
static int dist_[MAXK][MAXN];             /* dist_[c][v], types are 1..k */
static int tmp_[MAXK];

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= INT_MAX &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        IntArray::full(arr, n, l1)
*/
;
// static int cmp_int(const void *a, const void *b)
// {
//     int x = *(const int *)a, y = *(const int *)b;
//     return (x > y) - (x < y);
// }

/* bfs_type: multi-source BFS from all towns producing type c, into dist. */
static void bfs_type(int n, const int *a, int c, int *dist)
/*@ With (m : Z) (edges : list (Z * Z)) (goods : list Z)
         (hd : list Z) (nx : list Z) (tlst : list Z) (dist_before : list Z)
    Require
      1 <= n && n <= 100000 && 0 <= m && m <= 100000 &&
      1 <= c && c <= 100 &&
      n == Zlength(goods) && m == Zlength(edges) &&
      AdjBuild(n, m, edges, hd, nx, tlst) &&
      NxtRange(m, nx) && ArcToRange(n, m, tlst) &&
      Zlength(dist_before) == 100005 &&
      IntArray::seg(a, 1, n + 1, goods) *
      IntArray::seg(head_, 1, n + 1, hd) *
      IntArray::full(nxt_, 2 * m, nx) *
      IntArray::full(to_, 2 * m, tlst) *
      IntArray::undef_full(queue_, n) *
      IntArray::full(dist, 100005, dist_before)
    Ensure
      exists dist_after,
        Zlength(dist_after) == 100005 &&
        BfsRowResult(n@pre, edges, goods, c@pre, dist_after) &&
        IntArray::seg(a@pre, 1, n@pre + 1, goods) *
        IntArray::seg(head_, 1, n@pre + 1, hd) *
        IntArray::full(nxt_, 2 * m, nx) *
        IntArray::full(to_, 2 * m, tlst) *
        IntArray::undef_full(queue_, n@pre) *
        IntArray::full(dist@pre, 100005, dist_after)
*/
{
    /*@ Inv Assert
          exists dl,
            n == n@pre && a == a@pre && c == c@pre && dist == dist@pre &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m && m <= 100000 &&
            1 <= c@pre && c@pre <= 100 &&
            n@pre == Zlength(goods) && m == Zlength(edges) &&
            AdjBuild(n@pre, m, edges, hd, nx, tlst) &&
            NxtRange(m, nx) && ArcToRange(n@pre, m, tlst) &&
            1 <= v && v <= n@pre + 1 &&
            Zlength(dl) == 100005 &&
            (forall w, (1 <= w && w < v) => Znth(w, dl, 0) == -1) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m, nx) *
            IntArray::full(to_, 2 * m, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::full(dist@pre, 100005, dl)
    */
    for (int v = 1; v <= n; v++)
        dist[v] = -1;
    int qh = 0, qt = 0;
    /*@ Inv Assert
          exists dl Q,
            n == n@pre && a == a@pre && c == c@pre && dist == dist@pre &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m && m <= 100000 &&
            1 <= c@pre && c@pre <= 100 &&
            n@pre == Zlength(goods) && m == Zlength(edges) &&
            AdjBuild(n@pre, m, edges, hd, nx, tlst) &&
            NxtRange(m, nx) && ArcToRange(n@pre, m, tlst) &&
            1 <= v && v <= n@pre + 1 &&
            qh == 0 && 0 <= qt && qt == Zlength(Q) && qt <= v - 1 &&
            Zlength(dl) == 100005 &&
            BfsInit(n@pre, goods, c@pre, Q, dl, v) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m, nx) *
            IntArray::full(to_, 2 * m, tlst) *
            IntArray::seg(queue_, 0, qt, Q) *
            IntArray::undef_seg(queue_, qt, n@pre) *
            IntArray::full(dist@pre, 100005, dl)
    */
    for (int v = 1; v <= n; v++)
        if (a[v] == c) {
            dist[v] = 0;
            queue_[qt] = v;
            qt = qt + 1;
        }
    /*@ Inv Assert
          exists dl Q,
            n == n@pre && a == a@pre && c == c@pre && dist == dist@pre &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m && m <= 100000 &&
            1 <= c@pre && c@pre <= 100 &&
            n@pre == Zlength(goods) && m == Zlength(edges) &&
            AdjBuild(n@pre, m, edges, hd, nx, tlst) &&
            NxtRange(m, nx) && ArcToRange(n@pre, m, tlst) &&
            0 <= qh && qh <= qt && qt == Zlength(Q) && qt <= n@pre &&
            Zlength(dl) == 100005 &&
            BfsCore(n@pre, edges, goods, c@pre, Q, dl) &&
            BfsExpanded(n@pre, edges, Q, dl, qh) &&
            ((qh < qt) =>
               BfsBounded(Q, dl, Znth(Znth(qh, Q, 0), dl, 0) + 1)) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m, nx) *
            IntArray::full(to_, 2 * m, tlst) *
            IntArray::seg(queue_, 0, qt, Q) *
            IntArray::undef_seg(queue_, qt, n@pre) *
            IntArray::full(dist@pre, 100005, dl)
    */
    while (qh < qt) {
        int u = queue_[qh];
        qh = qh + 1;
        /*@ Assert
              exists dl Q,
                n == n@pre && a == a@pre && c == c@pre && dist == dist@pre &&
                1 <= n@pre && n@pre <= 100000 && 0 <= m && m <= 100000 &&
                1 <= c@pre && c@pre <= 100 &&
                n@pre == Zlength(goods) && m == Zlength(edges) &&
                AdjBuild(n@pre, m, edges, hd, nx, tlst) &&
                NxtRange(m, nx) && ArcToRange(n@pre, m, tlst) &&
                1 <= qh && qh <= qt && qt == Zlength(Q) && qt <= n@pre &&
                u == Znth(qh - 1, Q, 0) && 1 <= u && u <= n@pre &&
                0 <= Znth(u, dl, 0) && Znth(u, dl, 0) <= n@pre - 1 &&
                Zlength(dl) == 100005 &&
                BfsCore(n@pre, edges, goods, c@pre, Q, dl) &&
                BfsExpanded(n@pre, edges, Q, dl, qh - 1) &&
                BfsBounded(Q, dl, Znth(u, dl, 0) + 1) &&
                IntArray::seg(a@pre, 1, n@pre + 1, goods) *
                IntArray::seg(head_, 1, n@pre + 1, hd) *
                IntArray::full(nxt_, 2 * m, nx) *
                IntArray::full(to_, 2 * m, tlst) *
                IntArray::seg(queue_, 0, qt, Q) *
                IntArray::undef_seg(queue_, qt, n@pre) *
                IntArray::full(dist@pre, 100005, dl)
        */
        /*@ Inv Assert
              exists dl Q,
                n == n@pre && a == a@pre && c == c@pre && dist == dist@pre &&
                1 <= n@pre && n@pre <= 100000 && 0 <= m && m <= 100000 &&
                1 <= c@pre && c@pre <= 100 &&
                n@pre == Zlength(goods) && m == Zlength(edges) &&
                AdjBuild(n@pre, m, edges, hd, nx, tlst) &&
                NxtRange(m, nx) && ArcToRange(n@pre, m, tlst) &&
                1 <= qh && qh <= qt && qt == Zlength(Q) && qt <= n@pre &&
                u == Znth(qh - 1, Q, 0) && 1 <= u && u <= n@pre &&
                0 <= Znth(u, dl, 0) && Znth(u, dl, 0) <= n@pre - 1 &&
                -1 <= e && e < 2 * m &&
                Zlength(dl) == 100005 &&
                ((e != -1) =>
                   (1 <= Znth(e, tlst, 0) && Znth(e, tlst, 0) <= n@pre)) &&
                ((e != -1 && Znth(Znth(e, tlst, 0), dl, 0) < 0) =>
                   qt < n@pre) &&
                BfsCore(n@pre, edges, goods, c@pre, Q, dl) &&
                BfsExpanded(n@pre, edges, Q, dl, qh - 1) &&
                BfsBounded(Q, dl, Znth(u, dl, 0) + 1) &&
                BfsScan(m, edges, nx, tlst, Q, dl, u, e) &&
                IntArray::seg(a@pre, 1, n@pre + 1, goods) *
                IntArray::seg(head_, 1, n@pre + 1, hd) *
                IntArray::full(nxt_, 2 * m, nx) *
                IntArray::full(to_, 2 * m, tlst) *
                IntArray::seg(queue_, 0, qt, Q) *
                IntArray::undef_seg(queue_, qt, n@pre) *
                IntArray::full(dist@pre, 100005, dl)
        */
        for (int e = head_[u]; e != -1; e = nxt_[e]) {
            int v = to_[e];
            if (dist[v] < 0) {
                dist[v] = dist[u] + 1;
                queue_[qt] = v;
                qt = qt + 1;
            }
        }
    }
}

/* solver: reads no input.  cost[v] = cheapest way for town v to collect s of
 * the k goods types, given the town types a[1..n] and the m roads eu[]-ev[].
 * Writes the file-scope work arrays above. */
static void solver(int n, int m, int k, int s, const int *a,
                   const int *eu, const int *ev, long long *cost)
/* QCP_INSERT_BEGIN:shard09-P051-solver-contract */
/*@ With (tree_edges : list (Z * Z)) (goods : list Z)
         (edge_u : list Z) (edge_v : list Z) (dist_before : list (list Z))
    Require
      Pre(k, s, tree_edges, goods) && 1 <= n && n <= 100000 && 0 <= m && m <= 100000 && 1 <= s && s <= k && k <= 100 && k <= n &&
      (forall i, (0 <= i && i < n) => (1 <= goods[i] && goods[i] <= k)) && (forall i, (0 <= i && i < Zlength(tree_edges)) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
      n == Zlength(goods) && m == Zlength(tree_edges) &&
      Zlength(edge_u) == m && Zlength(edge_v) == m &&
      (forall i, (0 <= i && i < m) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
      Zlength(dist_before) == 105 && (forall c, (0 <= c && c < 105) => Zlength(dist_before[c]) == 100005) &&
      IntArray::seg(a, 1, n + 1, goods) *
      IntArray::full(eu, m, edge_u) * IntArray::full(ev, m, edge_v) *
      Int64Array::undef_seg(cost, 1, n + 1) *
      IntArray::undef_seg(head_, 1, n + 1) *
      IntArray::undef_full(nxt_, 2 * m) * IntArray::undef_full(to_, 2 * m) *
      IntArray::undef_full(queue_, n) * IntArray::undef_full(tmp_, k) *
      IntArray2::full(dist_, 105, 100005, dist_before)
    Ensure
      exists (out : list Z) (head_after : list Z) (nxt_after : list Z) (to_after : list Z)
             (tmp_after : list Z) (dist_after : list (list Z)),
        Spec(k@pre, s@pre, tree_edges, goods, out) &&
        Zlength(out) == n &&
        Zlength(dist_after) == 105 && (forall c, (0 <= c && c < 105) => Zlength(dist_after[c]) == 100005) &&
        IntArray::seg(a, 1, n + 1, goods) *
        IntArray::full(eu, m, edge_u) * IntArray::full(ev, m, edge_v) *
        Int64Array::seg(cost, 1, n + 1, out) *
        IntArray::seg(head_, 1, n + 1, head_after) *
        IntArray::full(nxt_, 2 * m, nxt_after) * IntArray::full(to_, 2 * m, to_after) *
        IntArray::undef_full(queue_, n) * IntArray::full(tmp_, k, tmp_after) *
        IntArray2::full(dist_, 105, 100005, dist_after)
*/
/* QCP_INSERT_END:shard09-P051-solver-contract */
{
    /*@ Inv Assert
          exists hd0,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            1 <= v && v <= n@pre + 1 &&
            Zlength(hd0) == v - 1 &&
            (forall j, (0 <= j && j < v - 1) => hd0[j] == -1) &&
            Zlength(dist_before) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(dist_before[cc]) == 100005) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::undef_seg(cost@pre, 1, n@pre + 1) *
            IntArray::seg(head_, 1, v, hd0) *
            IntArray::undef_seg(head_, v, n@pre + 1) *
            IntArray::undef_full(nxt_, 2 * m@pre) *
            IntArray::undef_full(to_, 2 * m@pre) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::undef_full(tmp_, k@pre) *
            IntArray2::full(dist_, 105, 100005, dist_before)
    */
    for (int v = 1; v <= n; v++)
        head_[v] = -1;
    /*@ Inv Assert
          exists hd nx tlst,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            0 <= i && i <= m@pre &&
            ((i < m@pre) => (1 <= edge_u[i] && edge_u[i] <= n@pre &&
                             1 <= edge_v[i] && edge_v[i] <= n@pre)) &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * i && Zlength(tlst) == 2 * i &&
            AdjBuild(n@pre, i, tree_edges, hd, nx, tlst) &&
            NxtRange(i, nx) && ArcToRange(n@pre, i, tlst) &&
            Zlength(dist_before) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(dist_before[cc]) == 100005) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::undef_seg(cost@pre, 1, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::seg(nxt_, 0, 2 * i, nx) *
            IntArray::undef_seg(nxt_, 2 * i, 2 * m@pre) *
            IntArray::seg(to_, 0, 2 * i, tlst) *
            IntArray::undef_seg(to_, 2 * i, 2 * m@pre) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::undef_full(tmp_, k@pre) *
            IntArray2::full(dist_, 105, 100005, dist_before)
    */
    for (int i = 0; i < m; i++) {         /* undirected, two arcs per road */
        int e = 2 * i;
        to_[e] = ev[i]; nxt_[e] = head_[eu[i]]; head_[eu[i]] = e;
        to_[e + 1] = eu[i]; nxt_[e + 1] = head_[ev[i]]; head_[ev[i]] = e + 1;
    }
    /*@ Inv Assert
          exists hd nx tlst rows,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            1 <= c && c <= k@pre + 1 &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * m@pre && Zlength(tlst) == 2 * m@pre &&
            AdjBuild(n@pre, m@pre, tree_edges, hd, nx, tlst) &&
            NxtRange(m@pre, nx) && ArcToRange(n@pre, m@pre, tlst) &&
            Zlength(rows) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(rows[cc]) == 100005) &&
            BfsRows(n@pre, tree_edges, goods, rows, c) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::undef_seg(cost@pre, 1, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m@pre, nx) *
            IntArray::full(to_, 2 * m@pre, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::undef_full(tmp_, k@pre) *
            IntArray2::full(dist_, 105, 100005, rows)
    */
    for (int c = 1; c <= k; c++)
        /*@ Assert
              exists hd nx tlst rows,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            1 <= c && c <= k@pre &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * m@pre && Zlength(tlst) == 2 * m@pre &&
            AdjBuild(n@pre, m@pre, tree_edges, hd, nx, tlst) &&
            NxtRange(m@pre, nx) && ArcToRange(n@pre, m@pre, tlst) &&
            Zlength(rows) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(rows[cc]) == 100005) &&
            BfsRows(n@pre, tree_edges, goods, rows, c) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::undef_seg(cost@pre, 1, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m@pre, nx) *
            IntArray::full(to_, 2 * m@pre, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::undef_full(tmp_, k@pre) *
            IntArray2::missing_i(dist_, c, 0, 105, 100005, rows) *
            IntArray::full(pointer_offset(pointer_offset(dist_, c, int[100005]), 0, int), 100005, rows[c])
        */
        bfs_type(n, a, c, dist_[c])
        /*@ where m = m@pre, edges = tree_edges, goods = goods */;
    /*@ Inv Assert
          (exists hd nx tlst rows out,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            v == 1 && Zlength(out) == 0 &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * m@pre && Zlength(tlst) == 2 * m@pre &&
            Zlength(rows) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(rows[cc]) == 100005) &&
            BfsRows(n@pre, tree_edges, goods, rows, k@pre + 1) &&
            OutPrefix(n@pre, s@pre, tree_edges, goods, out, v - 1) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::seg(cost@pre, 1, v, out) *
            Int64Array::undef_seg(cost@pre, v, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m@pre, nx) *
            IntArray::full(to_, 2 * m@pre, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::undef_full(tmp_, k@pre) *
            IntArray2::full(dist_, 105, 100005, rows))
          ||
          (exists hd nx tlst rows out tmpl,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            2 <= v && v <= n@pre + 1 && Zlength(out) == v - 1 &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * m@pre && Zlength(tlst) == 2 * m@pre &&
            Zlength(rows) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(rows[cc]) == 100005) &&
            BfsRows(n@pre, tree_edges, goods, rows, k@pre + 1) &&
            OutPrefix(n@pre, s@pre, tree_edges, goods, out, v - 1) &&
            Zlength(tmpl) == k@pre &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::seg(cost@pre, 1, v, out) *
            Int64Array::undef_seg(cost@pre, v, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m@pre, nx) *
            IntArray::full(to_, 2 * m@pre, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::full(tmp_, k@pre, tmpl) *
            IntArray2::full(dist_, 105, 100005, rows))
    */
    for (int v = 1; v <= n; v++) {
        /*@ Inv Assert
              exists hd nx tlst rows out tp,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            1 <= v && v <= n@pre && Zlength(out) == v - 1 &&
            1 <= c && c <= k@pre + 1 &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * m@pre && Zlength(tlst) == 2 * m@pre &&
            Zlength(rows) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(rows[cc]) == 100005) &&
            BfsRows(n@pre, tree_edges, goods, rows, k@pre + 1) &&
            OutPrefix(n@pre, s@pre, tree_edges, goods, out, v - 1) &&
            Zlength(tp) == c - 1 &&
            TmpPrefix(n@pre, tree_edges, goods, v, tp, c - 1) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::seg(cost@pre, 1, v, out) *
            Int64Array::undef_seg(cost@pre, v, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m@pre, nx) *
            IntArray::full(to_, 2 * m@pre, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::seg(tmp_, 0, c - 1, tp) *
            IntArray::undef_seg(tmp_, c - 1, k@pre) *
            IntArray2::full(dist_, 105, 100005, rows)
        */
        for (int c = 1; c <= k; c++)
            tmp_[c - 1] = dist_[c][v];
        /*@ Assert
              exists hd nx tlst rows out tp,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            1 <= v && v <= n@pre && Zlength(out) == v - 1 &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * m@pre && Zlength(tlst) == 2 * m@pre &&
            Zlength(rows) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(rows[cc]) == 100005) &&
            BfsRows(n@pre, tree_edges, goods, rows, k@pre + 1) &&
            OutPrefix(n@pre, s@pre, tree_edges, goods, out, v - 1) &&
            TmpPrefix(n@pre, tree_edges, goods, v, tp, k@pre) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::seg(cost@pre, 1, v, out) *
            Int64Array::undef_seg(cost@pre, v, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m@pre, nx) *
            IntArray::full(to_, 2 * m@pre, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::full(pointer_offset(tmp_, 0, int), k@pre, tp) *
            IntArray2::full(dist_, 105, 100005, rows)
        */
        // qsort(tmp_, k, sizeof *tmp_, cmp_int);
        quicksort(tmp_, k);
        long long sum = 0;
        /*@ Inv Assert
              exists hd nx tlst rows out l1,
            n == n@pre && m == m@pre && k == k@pre && s == s@pre &&
            a == a@pre && eu == eu@pre && ev == ev@pre && cost == cost@pre &&
            Pre(k@pre, s@pre, tree_edges, goods) &&
            1 <= n@pre && n@pre <= 100000 && 0 <= m@pre && m@pre <= 100000 &&
            1 <= s@pre && s@pre <= k@pre && k@pre <= 100 && k@pre <= n@pre &&
            (forall i, (0 <= i && i < n@pre) => (1 <= goods[i] && goods[i] <= k@pre)) &&
            (forall i, (0 <= i && i < m@pre) => (1 <= fst(tree_edges[i]) && fst(tree_edges[i]) <= n@pre && 1 <= snd(tree_edges[i]) && snd(tree_edges[i]) <= n@pre && fst(tree_edges[i]) != snd(tree_edges[i]))) &&
            n@pre == Zlength(goods) && m@pre == Zlength(tree_edges) &&
            Zlength(edge_u) == m@pre && Zlength(edge_v) == m@pre &&
            (forall i, (0 <= i && i < m@pre) => (edge_u[i] == fst(tree_edges[i]) && edge_v[i] == snd(tree_edges[i]))) &&
            1 <= v && v <= n@pre && Zlength(out) == v - 1 &&
            0 <= i && i <= s@pre &&
            Zlength(hd) == n@pre && Zlength(nx) == 2 * m@pre && Zlength(tlst) == 2 * m@pre &&
            Zlength(rows) == 105 &&
            (forall cc, (0 <= cc && cc < 105) => Zlength(rows[cc]) == 100005) &&
            BfsRows(n@pre, tree_edges, goods, rows, k@pre + 1) &&
            OutPrefix(n@pre, s@pre, tree_edges, goods, out, v - 1) &&
            Zlength(l1) == k@pre && mono_nondec(l1) &&
            (exists tp0, Zlength(tp0) == k@pre &&
               TmpPrefix(n@pre, tree_edges, goods, v, tp0, k@pre) &&
               Permutation(tp0, l1)) &&
            (forall j, (0 <= j && j < k@pre) => (0 <= l1[j] && l1[j] <= n@pre - 1)) &&
            sum == ZSum(sublist(0, i, l1)) &&
            IntArray::seg(a@pre, 1, n@pre + 1, goods) *
            IntArray::full(eu@pre, m@pre, edge_u) *
            IntArray::full(ev@pre, m@pre, edge_v) *
            Int64Array::seg(cost@pre, 1, v, out) *
            Int64Array::undef_seg(cost@pre, v, n@pre + 1) *
            IntArray::seg(head_, 1, n@pre + 1, hd) *
            IntArray::full(nxt_, 2 * m@pre, nx) *
            IntArray::full(to_, 2 * m@pre, tlst) *
            IntArray::undef_full(queue_, n@pre) *
            IntArray::full(tmp_, k@pre, l1) *
            IntArray2::full(dist_, 105, 100005, rows)
        */
        for (int i = 0; i < s; i++)
            sum += tmp_[i];
        cost[v] = sum;
    }
}

// int main(void)
// {
//     int n, m, k, s;
//     if (scanf("%d %d %d %d", &n, &m, &k, &s) != 4)
//         return 0;
//     static int a[MAXN], eu[MAXM], ev[MAXM];
//     static long long cost[MAXN];
//     for (int v = 1; v <= n; v++)
//         scanf("%d", &a[v]);
//     for (int i = 0; i < m; i++)
//         scanf("%d %d", &eu[i], &ev[i]);
//     solver(n, m, k, s, a, eu, ev, cost);
//     for (int v = 1; v <= n; v++)
//         printf("%lld%c", cost[v], v == n ? '\n' : ' ');
//     return 0;
// }
