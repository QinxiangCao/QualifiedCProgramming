/* Codeforces 1946/C - Tree Cutting */
// #include <stdio.h>
// #include <stdlib.h>

static int n, k, *head, *to, *next_edge, *parent, *order, *size_sub;

/* QCP_INSERT_BEGIN:P049_1946C_tree_cutting.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : Z -> Z -> list (Z*Z) -> Prop)
      (Spec : Z -> Z -> list (Z*Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::seg_shape : Z -> Z -> Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
      (AdjacencyBuildState : Z -> list (Z*Z) -> Z -> list Z -> list Z -> list Z -> Prop)
      (AdjacencyModel : Z -> list (Z*Z) -> list Z -> list Z -> list Z -> Prop)
      (CurrentEdgeFresh : list (Z*Z) -> Z -> Prop)
      (TreeAttachmentCut : list (Z*Z) -> Prop)
      (TraversalState : Z -> list (Z*Z) -> Z -> list Z -> list (option Z) -> Prop)
      (TraversalEntryState : Z -> list (Z*Z) -> Z -> list Z -> list (option Z) -> Prop)
      (TraversalAdjState : Z -> list (Z*Z) -> Z -> list Z -> list (option Z) ->
                           list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (RootedOrderModel : Z -> list (Z*Z) -> list Z -> list Z -> Prop)
      (FreshSizeCells : Z -> list (option Z) -> Prop)
      (SizeInitializationState : Z -> Z -> list Z -> Prop)
      (CutScanState : Z -> Z -> list (Z*Z) -> Z -> Z -> Z -> list Z -> list Z -> list Z -> Prop)
      (ThresholdFeasible : Z -> Z -> list (Z*Z) -> Z -> Prop)
      (SearchState : Z -> Z -> list (Z*Z) -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P049_1946C_tree_cutting_lib */
/* QCP_INSERT_END:P049_1946C_tree_cutting.support */

/* QCP uses one named contract at each allocation site.  Keeping the six
 * contracts distinct makes the ownership introduced at each global pointer
 * assignment explicit. */
void *malloc(unsigned long size)
/*@ malloc_head
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_to
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_next_edge
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_parent
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_order
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_size_sub
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure exists cells,
           __return != 0 && FreshSizeCells(cap, cells) &&
           Zlength(cells) == cap &&
           IntArray::mixed_full(__return, cap, cells)
*/;

void free(void *ptr)
/*@ free_head
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_to
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_next_edge
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_parent
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_order
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_size_sub
    With (cap : Z)
    Require 0 <= cap && IntArray::undef_full(ptr, cap)
    Ensure emp
*/;

static int feasible(int minimum)
/*@ With (nv kv : Z) (edges : list (Z*Z))
             (head_p to_p next_p parent_p order_p size_p : Z)
             (head_data to_data next_data parent_data order_data : list Z)
    Require
      1 <= minimum && minimum <= nv &&
      1 <= kv && kv < nv && nv <= 100000 &&
      Pre(nv, kv, edges) &&
      AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
      RootedOrderModel(nv, edges, parent_data, order_data) &&
      Zlength(head_data) == nv && Zlength(parent_data) == nv &&
      Zlength(order_data) == nv &&
      Zlength(to_data) == 2 * nv - 2 && Zlength(next_data) == 2 * nv - 2 &&
      (forall j, (0 <= j && j < nv) =>
        (0 <= order_data[j] && order_data[j] < nv &&
         -1 <= parent_data[j] && parent_data[j] < nv)) &&
      store(&n, int, nv) * store(&k, int, kv) *
      store(&head, int *, head_p) * store(&to, int *, to_p) *
      store(&next_edge, int *, next_p) *
      store(&parent, int *, parent_p) * store(&order, int *, order_p) *
      store(&size_sub, int *, size_p) *
      IntArray::full(head_p, nv, head_data) *
      IntArray::full(to_p, 2 * nv - 2, to_data) *
      IntArray::full(next_p, 2 * nv - 2, next_data) *
      IntArray::full(parent_p, nv, parent_data) *
      IntArray::full(order_p, nv, order_data) *
      IntArray::undef_full(size_p, nv)
    Ensure
      0 <= __return && __return <= 1 &&
      (__return != 0 <=> ThresholdFeasible(nv, kv, edges, minimum)) &&
      (forall j, (0 <= j && j < nv) =>
        (0 <= order_data[j] && order_data[j] < nv &&
         -1 <= parent_data[j] && parent_data[j] < nv)) &&
      store(&n, int, nv) * store(&k, int, kv) *
      store(&head, int *, head_p) * store(&to, int *, to_p) *
      store(&next_edge, int *, next_p) *
      store(&parent, int *, parent_p) * store(&order, int *, order_p) *
      store(&size_sub, int *, size_p) *
      IntArray::full(head_p, nv, head_data) *
      IntArray::full(to_p, 2 * nv - 2, to_data) *
      IntArray::full(next_p, 2 * nv - 2, next_data) *
      IntArray::full(parent_p, nv, parent_data) *
      IntArray::full(order_p, nv, order_data) *
      IntArray::undef_full(size_p, nv)
*/
{
    /*@ Inv Assert
          exists initialized,
          minimum == minimum@pre &&
          1 <= minimum@pre && minimum@pre <= nv &&
          SizeInitializationState(nv, i, initialized) &&
          Pre(nv, kv, edges) &&
          AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
          RootedOrderModel(nv, edges, parent_data, order_data) &&
          (forall j, (0 <= j && j < nv) =>
            (0 <= order_data[j] && order_data[j] < nv &&
             -1 <= parent_data[j] && parent_data[j] < nv)) &&
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_p) * store(&order, int *, order_p) *
          store(&size_sub, int *, size_p) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data) *
          IntArray::full(parent_p, nv, parent_data) *
          IntArray::full(order_p, nv, order_data) *
          IntArray::seg(size_p, 0, i, initialized) *
          IntArray::undef_seg(size_p, i, nv)
    */
    for (int i = 0; i < n; ++i)
        size_sub[i] = 1;

    int components = 0;
    /*@ Inv Assert
          exists sizes,
          minimum == minimum@pre &&
          1 <= minimum@pre && minimum@pre <= nv &&
          -1 <= oi && oi < nv &&
          0 <= components && components <= nv - 1 - oi &&
          Zlength(sizes) == nv &&
          (forall j, (0 <= j && j < nv) =>
            (0 <= sizes[j] && sizes[j] <= nv)) &&
          ((oi >= 0 && parent_data[order_data[oi]] >= 0) =>
            sizes[parent_data[order_data[oi]]] +
              sizes[order_data[oi]] <= nv) &&
          Pre(nv, kv, edges) &&
          AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
          RootedOrderModel(nv, edges, parent_data, order_data) &&
          (forall j, (0 <= j && j < nv) =>
            (0 <= order_data[j] && order_data[j] < nv &&
             -1 <= parent_data[j] && parent_data[j] < nv)) &&
          CutScanState(nv, kv, edges, minimum@pre, oi, components,
                       parent_data, order_data, sizes) &&
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_p) * store(&order, int *, order_p) *
          store(&size_sub, int *, size_p) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data) *
          IntArray::full(parent_p, nv, parent_data) *
          IntArray::full(order_p, nv, order_data) *
          IntArray::full(size_p, nv, sizes)
    */
    for (int oi = n - 1; oi >= 0; --oi) {
        int v = order[oi];
        if (size_sub[v] >= minimum) {
            ++components;
            size_sub[v] = 0;
        }
        if (parent[v] >= 0)
            size_sub[parent[v]] += size_sub[v];
    }

    return components >= k + 1;
}

static int solver(int nn, int kk, const int *eu, const int *ev)/* QCP_INSERT_BEGIN:P049_1946C_tree_cutting.contract */

/*@ With (nv : Z)
             (kv : Z)
             (edges : list (Z*Z))
             (eu_data ev_data : list Z)
             (n_before k_before : Z)
             (head_before to_before next_before : Z)
             (parent_before order_before size_before : Z)
    Require
      1 <= kv && kv < nv &&
      nv <= 100000 &&
      Zlength(edges)==nv-1 &&
      (forall i, (0 <= i && i < Zlength(edges)) => ((1 <= fst(edges[i]) && fst(edges[i]) <= nv) && (1 <= snd(edges[i]) && snd(edges[i]) <= nv))) &&
      Pre(nv, kv, edges) &&
      nn == nv && kk == kv &&
      Zlength(eu_data) == Zlength(edges) && Zlength(ev_data) == Zlength(edges) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (eu_data[i] == fst(edges[i]) - 1 && ev_data[i] == snd(edges[i]) - 1)) &&
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      store(&n, int, n_before) * store(&k, int, k_before) *
      store(&head, int *, head_before) * store(&to, int *, to_before) *
      store(&next_edge, int *, next_before) *
      store(&parent, int *, parent_before) * store(&order, int *, order_before) *
      store(&size_sub, int *, size_before)
    Ensure
      exists head_after to_after next_after parent_after order_after size_after,
      Spec(nv, kv, edges, __return) &&
      eu == eu@pre && ev == ev@pre &&
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      store(&n, int, nv) * store(&k, int, kv) *
      store(&head, int *, head_after) * store(&to, int *, to_after) *
      store(&next_edge, int *, next_after) *
      store(&parent, int *, parent_after) *
      store(&order, int *, order_after) *
      store(&size_sub, int *, size_after)
*/
/* QCP_INSERT_END:P049_1946C_tree_cutting.contract */

{
    n = nn;
    k = kk;

    head = malloc(n * sizeof(*head))
      /*@ where (malloc_head) cap = n */;
    to = malloc((2 * n - 2) * sizeof(*to))
      /*@ where (malloc_to) cap = 2 * n - 2 */;
    next_edge = malloc((2 * n - 2) * sizeof(*next_edge))
      /*@ where (malloc_next_edge) cap = 2 * n - 2 */;

    /*@ Inv Assert
          exists head_p to_p next_p head_init,
          nn == nv && kk == kv &&
          eu == eu@pre && ev == ev@pre &&
          1 <= kv && kv < nv && nv <= 100000 &&
          Pre(nv, kv, edges) &&
          0 <= i && i <= nv && Zlength(head_init) == i &&
          (forall q, (0 <= q && q < i) => head_init[q] == -1) &&
          (forall j, (0 <= j && j < nv - 1) =>
            (0 <= eu_data[j] && eu_data[j] < nv &&
             0 <= ev_data[j] && ev_data[j] < nv &&
             eu_data[j] == fst(edges[j]) - 1 &&
             ev_data[j] == snd(edges[j]) - 1)) &&
          IntArray::full(eu, nv - 1, eu_data) *
          IntArray::full(ev, nv - 1, ev_data) *
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_before) * store(&order, int *, order_before) *
          store(&size_sub, int *, size_before) *
          IntArray::seg(head_p, 0, i, head_init) *
          IntArray::undef_seg(head_p, i, nv) *
          IntArray::undef_full(to_p, 2 * nv - 2) *
          IntArray::undef_full(next_p, 2 * nv - 2)
    */
    for (int i = 0; i < n; ++i)
        head[i] = -1;

    int ec = 0;
    /*@ Inv Assert
          exists head_p to_p next_p head_data to_done next_done,
          nn == nv && kk == kv &&
          eu == eu@pre && ev == ev@pre &&
          1 <= kv && kv < nv && nv <= 100000 &&
          Pre(nv, kv, edges) &&
          0 <= i && i <= nv - 1 && ec == 2 * i &&
          Zlength(head_data) == nv &&
          Zlength(to_done) == ec && Zlength(next_done) == ec &&
          AdjacencyBuildState(nv, edges, i, head_data, to_done, next_done) &&
          CurrentEdgeFresh(edges, i) &&
          (forall j, (0 <= j && j < nv - 1) =>
            (0 <= eu_data[j] && eu_data[j] < nv &&
             0 <= ev_data[j] && ev_data[j] < nv &&
             eu_data[j] == fst(edges[j]) - 1 &&
             ev_data[j] == snd(edges[j]) - 1)) &&
          IntArray::full(eu, nv - 1, eu_data) *
          IntArray::full(ev, nv - 1, ev_data) *
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_before) * store(&order, int *, order_before) *
          store(&size_sub, int *, size_before) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::seg(to_p, 0, ec, to_done) *
          IntArray::undef_seg(to_p, ec, 2 * nv - 2) *
          IntArray::seg(next_p, 0, ec, next_done) *
          IntArray::undef_seg(next_p, ec, 2 * nv - 2)
    */
    for (int i = 0; i + 1 < n; ++i) {
        int u = eu[i], v = ev[i];

        to[ec] = v;
        next_edge[ec] = head[u];
        head[u] = ec;
        ec++;

        to[ec] = u;
        next_edge[ec] = head[v];
        head[v] = ec;
        ec++;
    }

    /*@ Assert
          exists head_p to_p next_p head_data to_data next_data,
          nn == nv && kk == kv && ec == 2 * nv - 2 &&
          1 <= kv && kv < nv && nv <= 100000 &&
          eu == eu@pre && ev == ev@pre &&
          Pre(nv, kv, edges) &&
          AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
          Zlength(head_data) == nv &&
          Zlength(to_data) == 2 * nv - 2 && Zlength(next_data) == 2 * nv - 2 &&
          IntArray::full(eu, nv - 1, eu_data) *
          IntArray::full(ev, nv - 1, ev_data) *
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_before) * store(&order, int *, order_before) *
          store(&size_sub, int *, size_before) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data)
    */
    parent = malloc(n * sizeof(*parent))
      /*@ where (malloc_parent) cap = n */;
    order = malloc(n * sizeof(*order))
      /*@ where (malloc_order) cap = n */;
    size_sub = malloc(n * sizeof(*size_sub))
      /*@ where (malloc_size_sub) cap = n */;

    int top = 1;
    order[0] = 0;
    parent[0] = -1;

    /*@ Inv Assert
          exists head_p to_p next_p parent_p order_p size_p,
          exists head_data to_data next_data order_data parent_cells,
          eu == eu@pre && ev == ev@pre &&
          nn == nv && kk == kv && ec == 2 * nv - 2 &&
          1 <= top && top <= nv && 0 <= i && i <= top &&
          Zlength(head_data) == nv &&
          Zlength(to_data) == 2 * nv - 2 &&
          Zlength(next_data) == 2 * nv - 2 &&
          Zlength(order_data) == top && Zlength(parent_cells) == nv &&
          (forall q, (0 <= q && q < top) =>
            (0 <= order_data[q] && order_data[q] < nv &&
             exists pv, parent_cells[order_data[q]] == Some(pv) &&
                        -1 <= pv && pv < nv)) &&
          (forall q, (0 <= q && q < 2 * nv - 2) =>
            (0 <= to_data[q] && to_data[q] < nv &&
             -1 <= next_data[q] && next_data[q] < 2 * nv - 2)) &&
          Pre(nv, kv, edges) &&
          TreeAttachmentCut(edges) &&
          AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
          TraversalEntryState(nv, edges, i, order_data, parent_cells) &&
          IntArray::full(eu, nv - 1, eu_data) *
          IntArray::full(ev, nv - 1, ev_data) *
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_p) * store(&order, int *, order_p) *
          store(&size_sub, int *, size_p) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data) *
          IntArray::mixed_full(parent_p, nv, parent_cells) *
          IntArray::seg(order_p, 0, top, order_data) *
          IntArray::undef_seg(order_p, top, nv) *
          IntArray::undef_full(size_p, nv)
    */
    for (int i = 0; i < top; ++i) {
        int v = order[i];
        /*@ Assert
              exists head_p to_p next_p parent_p order_p size_p,
              exists head_data to_data next_data order_data parent_cells parent_v,
              eu == eu@pre && ev == ev@pre &&
              nn == nv && kk == kv && ec == 2 * nv - 2 &&
              0 <= i && i < top && 1 <= top && top <= nv &&
              0 <= v && v < nv && v == order_data[i] &&
              -1 <= parent_v && parent_v < nv &&
              parent_cells[v] == Some(parent_v) &&
              Zlength(head_data) == nv &&
              Zlength(to_data) == 2 * nv - 2 &&
              Zlength(next_data) == 2 * nv - 2 &&
              Zlength(order_data) == top && Zlength(parent_cells) == nv &&
              (forall q, (0 <= q && q < top) =>
                (0 <= order_data[q] && order_data[q] < nv &&
                 exists pv, parent_cells[order_data[q]] == Some(pv) &&
                            -1 <= pv && pv < nv)) &&
              (forall q, (0 <= q && q < 2 * nv - 2) =>
                (0 <= to_data[q] && to_data[q] < nv &&
                 -1 <= next_data[q] && next_data[q] < 2 * nv - 2)) &&
              Pre(nv, kv, edges) &&
              TreeAttachmentCut(edges) &&
              AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
              TraversalEntryState(nv, edges, i, order_data, parent_cells) &&
              IntArray::full(eu, nv - 1, eu_data) *
              IntArray::full(ev, nv - 1, ev_data) *
              store(&n, int, nv) * store(&k, int, kv) *
              store(&head, int *, head_p) * store(&to, int *, to_p) *
              store(&next_edge, int *, next_p) *
              store(&parent, int *, parent_p) * store(&order, int *, order_p) *
              store(&size_sub, int *, size_p) *
              IntArray::full(head_p, nv, head_data) *
              IntArray::full(to_p, 2 * nv - 2, to_data) *
              IntArray::full(next_p, 2 * nv - 2, next_data) *
              store(pointer_offset(parent_p, v, int),
                    int, parent_v) *
              IntArray::mixed_missing_i(parent_p, v, 0, nv, parent_cells) *
              IntArray::seg(order_p, 0, top, order_data) *
              IntArray::undef_seg(order_p, top, nv) *
              IntArray::undef_full(size_p, nv)
        */
        int traversal_parent = parent[v];
        /*@ Inv Assert
              exists head_p to_p next_p parent_p order_p size_p,
              exists head_data to_data next_data order_data parent_cells parent_v,
              eu == eu@pre && ev == ev@pre &&
              nn == nv && kk == kv && ec == 2 * nv - 2 &&
              0 <= i && i < top && 1 <= top && top <= nv &&
              0 <= v && v < nv && -1 <= parent_v && parent_v < nv &&
              v == order_data[i] && traversal_parent == parent_v &&
              parent_cells[v] == Some(parent_v) &&
              -1 <= e && e < 2 * nv - 2 &&
              Zlength(head_data) == nv &&
              Zlength(to_data) == 2 * nv - 2 &&
              Zlength(next_data) == 2 * nv - 2 &&
              Zlength(order_data) == top && Zlength(parent_cells) == nv &&
              (forall q, (0 <= q && q < top) =>
                (0 <= order_data[q] && order_data[q] < nv &&
                 exists pv, parent_cells[order_data[q]] == Some(pv) &&
                            -1 <= pv && pv < nv)) &&
              (forall q, (0 <= q && q < 2 * nv - 2) =>
                (0 <= to_data[q] && to_data[q] < nv &&
                 -1 <= next_data[q] && next_data[q] < 2 * nv - 2)) &&
              Pre(nv, kv, edges) &&
              TreeAttachmentCut(edges) &&
              AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
              TraversalAdjState(nv, edges, i, order_data, parent_cells,
                                head_data, to_data, next_data,
                                v, parent_v, e) &&
              ((e != -1 && to_data[e] != parent_v) => top < nv) &&
              IntArray::full(eu, nv - 1, eu_data) *
              IntArray::full(ev, nv - 1, ev_data) *
              store(&n, int, nv) * store(&k, int, kv) *
              store(&head, int *, head_p) * store(&to, int *, to_p) *
              store(&next_edge, int *, next_p) *
              store(&parent, int *, parent_p) * store(&order, int *, order_p) *
              store(&size_sub, int *, size_p) *
              IntArray::full(head_p, nv, head_data) *
              IntArray::full(to_p, 2 * nv - 2, to_data) *
              IntArray::full(next_p, 2 * nv - 2, next_data) *
              IntArray::mixed_full(parent_p, nv, parent_cells) *
              IntArray::seg(order_p, 0, top, order_data) *
              IntArray::undef_seg(order_p, top, nv) *
              IntArray::undef_full(size_p, nv)
        */
        for (int e = head[v]; e != -1; e = next_edge[e])
            if (to[e] != traversal_parent) {
                /*@ top < nv by local */
                parent[to[e]] = v;
                order[top] = to[e];
                top++;
            }
    }

    int lo = 1;
    int hi = n / (k + 1);
    int ans = 1;

    /*@ Assert
          exists head_p to_p next_p parent_p order_p size_p,
          exists head_data to_data next_data parent_data order_data,
          eu == eu@pre && ev == ev@pre &&
          nn == nv && kk == kv && ec == 2 * nv - 2 && top == nv &&
          1 <= kv && kv < nv && nv <= 100000 &&
          Zlength(head_data) == nv && Zlength(parent_data) == nv &&
          Zlength(order_data) == nv &&
          Zlength(to_data) == 2 * nv - 2 && Zlength(next_data) == 2 * nv - 2 &&
          (forall j, (0 <= j && j < nv) =>
            (0 <= order_data[j] && order_data[j] < nv &&
             -1 <= parent_data[j] && parent_data[j] < nv)) &&
          Pre(nv, kv, edges) &&
          AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
          RootedOrderModel(nv, edges, parent_data, order_data) &&
          SearchState(nv, kv, edges, lo, hi, ans) &&
          IntArray::full(eu, nv - 1, eu_data) *
          IntArray::full(ev, nv - 1, ev_data) *
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_p) * store(&order, int *, order_p) *
          store(&size_sub, int *, size_p) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data) *
          IntArray::full(parent_p, nv, parent_data) *
          IntArray::full(order_p, nv, order_data) *
          IntArray::undef_full(size_p, nv)
    */
    /*@ Inv Assert
          exists head_p to_p next_p parent_p order_p size_p,
          exists head_data to_data next_data parent_data order_data,
          eu == eu@pre && ev == ev@pre &&
          nn == nv && kk == kv && ec == 2 * nv - 2 && top == nv &&
          1 <= lo && lo <= nv + 1 && 0 <= hi && hi <= nv &&
          1 <= ans && ans <= nv &&
          Zlength(head_data) == nv && Zlength(parent_data) == nv &&
          Zlength(order_data) == nv &&
          Zlength(to_data) == 2 * nv - 2 && Zlength(next_data) == 2 * nv - 2 &&
          (forall j, (0 <= j && j < nv) =>
            (0 <= order_data[j] && order_data[j] < nv &&
             -1 <= parent_data[j] && parent_data[j] < nv)) &&
          Pre(nv, kv, edges) &&
          AdjacencyModel(nv, edges, head_data, to_data, next_data) &&
          RootedOrderModel(nv, edges, parent_data, order_data) &&
          SearchState(nv, kv, edges, lo, hi, ans) &&
          IntArray::full(eu, nv - 1, eu_data) *
          IntArray::full(ev, nv - 1, ev_data) *
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_p) * store(&order, int *, order_p) *
          store(&size_sub, int *, size_p) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data) *
          IntArray::full(parent_p, nv, parent_data) *
          IntArray::full(order_p, nv, order_data) *
          IntArray::undef_full(size_p, nv)
    */
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        /*@ Given head_p to_p next_p parent_p order_p size_p
                  head_data to_data next_data parent_data order_data */
        if (feasible(mid) /*@ where nv = nv, kv = kv, edges = edges,
                                head_p = head_p, to_p = to_p, next_p = next_p,
                                parent_p = parent_p, order_p = order_p, size_p = size_p,
                                head_data = head_data, to_data = to_data,
                                next_data = next_data, parent_data = parent_data,
                                order_data = order_data */) {
            ans = mid;
            lo = mid + 1;
        } else
            hi = mid - 1;
    }

    /*@ Assert
          exists head_p to_p next_p parent_p order_p size_p,
          exists head_data to_data next_data parent_data order_data,
          eu == eu@pre && ev == ev@pre &&
          nn == nv && kk == kv &&
          Spec(nv, kv, edges, ans) &&
          Pre(nv, kv, edges) &&
          ec == 2 * nv - 2 && top == nv &&
          1 <= lo && lo <= nv + 1 && 0 <= hi && hi < lo && hi <= nv &&
          Zlength(head_data) == nv && Zlength(parent_data) == nv &&
          Zlength(order_data) == nv &&
          Zlength(to_data) == 2 * nv - 2 && Zlength(next_data) == 2 * nv - 2 &&
          IntArray::full(eu, nv - 1, eu_data) *
          IntArray::full(ev, nv - 1, ev_data) *
          store(&n, int, nv) * store(&k, int, kv) *
          store(&head, int *, head_p) * store(&to, int *, to_p) *
          store(&next_edge, int *, next_p) *
          store(&parent, int *, parent_p) * store(&order, int *, order_p) *
          store(&size_sub, int *, size_p) *
          IntArray::full(head_p, nv, head_data) *
          IntArray::full(to_p, 2 * nv - 2, to_data) *
          IntArray::full(next_p, 2 * nv - 2, next_data) *
          IntArray::full(parent_p, nv, parent_data) *
          IntArray::full(order_p, nv, order_data) *
          IntArray::undef_full(size_p, nv)
    */
    /*@ Given head_data to_data next_data parent_data order_data */
    free(head) /*@ where (free_head) cap = nv, values = head_data */;
    free(to) /*@ where (free_to) cap = 2 * nv - 2, values = to_data */;
    free(next_edge) /*@ where (free_next_edge) cap = 2 * nv - 2, values = next_data */;
    free(parent) /*@ where (free_parent) cap = nv, values = parent_data */;
    free(order) /*@ where (free_order) cap = nv, values = order_data */;
    free(size_sub) /*@ where (free_size_sub) cap = nv */;

    return ans;
}

// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--) {
//         scanf("%d %d", &n, &k);
//         int *eu = malloc((size_t)(n - 1) * sizeof(*eu)),
//             *ev = malloc((size_t)(n - 1) * sizeof(*ev));
//         for (int i = 0; i + 1 < n; ++i) {
//             scanf("%d %d", &eu[i], &ev[i]);
//             --eu[i];
//             --ev[i];
//         }
//         printf("%d\n", solver(n, k, eu, ev));
//         free(eu);
//         free(ev);
//     }
//     return 0;
// }
