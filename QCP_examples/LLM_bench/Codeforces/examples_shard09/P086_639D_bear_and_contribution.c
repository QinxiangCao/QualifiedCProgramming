/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_lib
*/

/*
 * Codeforces 639/D - Bear and Contribution  (rating 2400, GREEDY)
 *
 * Raising a user by d costs (d mod 5)*c + (d/5)*min(b, 5c): the remainder must
 * come from comments, and each further block of five is a blog or five
 * comments, whichever is cheaper.  Fix the target's residue mod 5 and sweep
 * the targets upward; every eligible user then costs base_i + (x/5)*W with a
 * fixed base, so a size-k max-heap of the smallest bases gives the best k.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P086-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P086_639D_bear_and_contribution_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> list Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P086-solver-support */
/*@ Extern Coq
      (ZSum : list Z -> Z)
      (HeapParent : Z -> Z)
      (HeapOrderedFrom : list Z -> Z -> Z -> Prop)
      (HeapOrdered : list Z -> Z -> Prop)
      (ZipPerm : list Z -> list Z -> list Z -> list Z -> Prop)
      (Nondecreasing : list Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (PushSiftState : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (PopSiftState : list Z -> list Z -> Z -> Z -> Prop)
      (SiftState : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (HeapSortState : list Z -> Z -> Z -> Prop)
      (ShiftedPrefix : list Z -> list Z -> Z -> Prop)
      (WCost : Z -> Z -> Z)
      (CandPrefix : list Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (HeapContent : list Z -> Z -> list Z -> Z -> Prop)
      (KSmallSum : list Z -> Z -> Z -> Prop)
      (SweepValue : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (TieCostAtResidue : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (ResidueBest : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (SweepBest : list Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
*/

#define SHIFT 2000000000LL

static void hpush(long long *heap, int *hsize, long long *hsum, long long v)
/*@ With (cap : Z) (l : list Z) (hs : Z) (sm : Z)
    Require
      0 <= hs && hs < cap && cap <= 200000 &&
      Zlength(l) == cap &&
      HeapOrdered(l, hs) &&
      sm == ZSum(sublist(0, hs, l)) &&
      (forall i, (0 <= i && i < hs) =>
        (-1000000000000 <= l[i] && l[i] <= 1000000000000)) &&
      -1000000000000 <= v && v <= 1000000000000 &&
      -300000000000000000 <= sm && sm <= 300000000000000000 &&
      Int64Array::full(heap, cap, l) *
      store_int(hsize, hs) * store_int64(hsum, sm)
    Ensure
      exists l1,
        Zlength(l1) == cap &&
        HeapOrdered(l1, hs + 1) &&
        Permutation(sublist(0, hs + 1, l1), cons(v, sublist(0, hs, l))) &&
        (forall i, (0 <= i && i < hs + 1) =>
          (-1000000000000 <= l1[i] && l1[i] <= 1000000000000)) &&
        Int64Array::full(heap, cap, l1) *
        store_int(hsize, hs + 1) * store_int64(hsum, sm + v)
*/
{
    int i = *hsize;
    *hsize = *hsize + 1;
    heap[i] = v;
    *hsum += v;
    /*@ Inv Assert
        exists cur,
          heap == heap@pre && hsize == hsize@pre && hsum == hsum@pre &&
          v == v@pre &&
          0 <= hs && hs < cap && cap <= 200000 && Zlength(l) == cap &&
          Zlength(cur) == cap &&
          0 <= i && i <= hs &&
          -1000000000000 <= v@pre && v@pre <= 1000000000000 &&
          -300000000000000000 <= sm && sm <= 300000000000000000 &&
          (forall q, (0 <= q && q < hs + 1) =>
            (-1000000000000 <= cur[q] && cur[q] <= 1000000000000)) &&
          PushSiftState(l, cur, hs, i, v@pre) &&
          Int64Array::full(heap, cap, cur) *
          store_int(hsize, hs + 1) * store_int64(hsum, sm + v@pre)
     */
    while (i > 0) {                       /* max-heap */
        int p = (i - 1) / 2;
        /*@ Assert
            exists cur,
              heap == heap@pre && hsize == hsize@pre && hsum == hsum@pre &&
              v == v@pre &&
              0 <= hs && hs < cap && cap <= 200000 && Zlength(l) == cap &&
              Zlength(cur) == cap &&
              0 < i && i <= hs &&
              0 <= p && p < i && p == HeapParent(i) &&
              -1000000000000 <= v@pre && v@pre <= 1000000000000 &&
              -300000000000000000 <= sm && sm <= 300000000000000000 &&
              (forall q, (0 <= q && q < hs + 1) =>
                (-1000000000000 <= cur[q] && cur[q] <= 1000000000000)) &&
              PushSiftState(l, cur, hs, i, v@pre) &&
              Int64Array::full(heap, cap, cur) *
              store_int(hsize, hs + 1) * store_int64(hsum, sm + v@pre)
         */
        if (heap[p] >= heap[i])
            break;
        long long t = heap[p]; heap[p] = heap[i]; heap[i] = t;
        i = p;
    }
}

static void hpop(long long *heap, int *hsize, long long *hsum)
/*@ With (cap : Z) (l : list Z) (hs : Z) (sm : Z)
    Require
      1 <= hs && hs <= cap && cap <= 200000 &&
      Zlength(l) == cap &&
      HeapOrdered(l, hs) &&
      sm == ZSum(sublist(0, hs, l)) &&
      (forall i, (0 <= i && i < hs) =>
        (-1000000000000 <= l[i] && l[i] <= 1000000000000)) &&
      -300000000000000000 <= sm && sm <= 300000000000000000 &&
      Int64Array::full(heap, cap, l) *
      store_int(hsize, hs) * store_int64(hsum, sm)
    Ensure
      exists l1,
        Zlength(l1) == cap &&
        HeapOrdered(l1, hs - 1) &&
        Permutation(sublist(0, hs, l), cons(l[0], sublist(0, hs - 1, l1))) &&
        (forall i, (0 <= i && i < hs) => (l[i] <= l[0])) &&
        (forall i, (0 <= i && i < hs - 1) =>
          (-1000000000000 <= l1[i] && l1[i] <= 1000000000000)) &&
        Int64Array::full(heap, cap, l1) *
        store_int(hsize, hs - 1) * store_int64(hsum, sm - l[0])
*/
{
    *hsum -= heap[0];
    *hsize = *hsize - 1;
    heap[0] = heap[*hsize];
    int i = 0;
    /*@ Inv Assert
        exists cur,
          heap == heap@pre && hsize == hsize@pre && hsum == hsum@pre &&
          1 <= hs && hs <= cap && cap <= 200000 && Zlength(l) == cap &&
          Zlength(cur) == cap &&
          0 <= i && (i == 0 || i < hs - 1) &&
          -300000000000000000 <= sm && sm <= 300000000000000000 &&
          (forall q, (0 <= q && q < hs) =>
            (-1000000000000 <= l[q] && l[q] <= 1000000000000)) &&
          (forall q, (0 <= q && q < hs) => (l[q] <= l[0])) &&
          (forall q, (0 <= q && q < hs - 1) =>
            (-1000000000000 <= cur[q] && cur[q] <= 1000000000000)) &&
          PopSiftState(l, cur, hs, i) &&
          Int64Array::full(heap, cap, cur) *
          store_int(hsize, hs - 1) * store_int64(hsum, sm - l[0])
     */
    while (1) {                           /* max-heap */
        int l = 2 * i + 1, r = l + 1, big = i;
        if (l < *hsize && heap[l] > heap[big]) big = l;
        if (r < *hsize && heap[r] > heap[big]) big = r;
        if (big == i)
            break;
        long long t = heap[big]; heap[big] = heap[i]; heap[i] = t;
        i = big;
    }
}

static void sift_candidates(long long *cand_t, long long *cand_base,
                            int root, int hi)
/*@ With (cap : Z) (t0 : list Z) (b0 : list Z) (tlo : Z) (thi : Z) (blo : Z) (bhi : Z)
    Require
      0 <= root && root <= hi && hi < cap && cap <= 200000 &&
      Zlength(t0) == cap && Zlength(b0) == cap &&
      HeapOrderedFrom(t0, hi + 1, root + 1) &&
      (forall i, (0 <= i && i < cap) =>
        (tlo <= t0[i] && t0[i] <= thi && blo <= b0[i] && b0[i] <= bhi)) &&
      Int64Array::full(cand_t, cap, t0) * Int64Array::full(cand_base, cap, b0)
    Ensure
      exists t1 b1,
        Zlength(t1) == cap && Zlength(b1) == cap &&
        HeapOrderedFrom(t1, hi + 1, root) &&
        ZipPerm(t0, b0, t1, b1) &&
        sublist(hi + 1, cap, t1) == sublist(hi + 1, cap, t0) &&
        sublist(hi + 1, cap, b1) == sublist(hi + 1, cap, b0) &&
        (forall i, (0 <= i && i < cap) =>
          (tlo <= t1[i] && t1[i] <= thi && blo <= b1[i] && b1[i] <= bhi)) &&
        Int64Array::full(cand_t, cap, t1) * Int64Array::full(cand_base, cap, b1)
*/
{
    /*@ Inv Assert
        exists t b,
          cand_t == cand_t@pre && cand_base == cand_base@pre && hi == hi@pre &&
          0 <= root@pre && root@pre <= root && root <= hi && hi < cap &&
          cap <= 200000 &&
          Zlength(t) == cap && Zlength(b) == cap &&
          (forall q, (0 <= q && q < cap) =>
            (tlo <= t[q] && t[q] <= thi && blo <= b[q] && b[q] <= bhi)) &&
          SiftState(t0, b0, t, b, hi + 1, root@pre, root) &&
          Int64Array::full(cand_t, cap, t) * Int64Array::full(cand_base, cap, b)
     */
    while (2 * root + 1 <= hi) {
        int child = 2 * root + 1;
        if (child + 1 <= hi && cand_t[child] < cand_t[child + 1])
            child++;
        if (cand_t[root] >= cand_t[child])
            return;
        long long v = cand_t[root]; cand_t[root] = cand_t[child];
        cand_t[child] = v;
        v = cand_base[root]; cand_base[root] = cand_base[child];
        cand_base[child] = v;
        root = child;
    }
}

static void sort_candidates(long long *cand_t, long long *cand_base, int n)
/*@ With (t0 : list Z) (b0 : list Z) (tlo : Z) (thi : Z) (blo : Z) (bhi : Z)
    Require
      0 <= n && n <= 200000 &&
      Zlength(t0) == n && Zlength(b0) == n &&
      (forall i, (0 <= i && i < n) =>
        (tlo <= t0[i] && t0[i] <= thi && blo <= b0[i] && b0[i] <= bhi)) &&
      Int64Array::full(cand_t, n, t0) * Int64Array::full(cand_base, n, b0)
    Ensure
      exists t1 b1,
        Zlength(t1) == n && Zlength(b1) == n &&
        ZipPerm(t0, b0, t1, b1) &&
        Nondecreasing(t1) &&
        (forall i, (0 <= i && i < n) =>
          (tlo <= t1[i] && t1[i] <= thi && blo <= b1[i] && b1[i] <= bhi)) &&
        Int64Array::full(cand_t, n, t1) * Int64Array::full(cand_base, n, b1)
*/
{
    /*@ Inv Assert
        exists t b,
          cand_t == cand_t@pre && cand_base == cand_base@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 200000 &&
          -1 <= root && root <= n@pre / 2 - 1 &&
          Zlength(t) == n@pre && Zlength(b) == n@pre &&
          (forall q, (0 <= q && q < n@pre) =>
            (tlo <= t[q] && t[q] <= thi && blo <= b[q] && b[q] <= bhi)) &&
          ZipPerm(t0, b0, t, b) &&
          HeapOrderedFrom(t, n@pre, root + 1) &&
          Int64Array::full(cand_t, n@pre, t) *
          Int64Array::full(cand_base, n@pre, b)
     */
    for (int root = n / 2 - 1; root >= 0; root--)
        /*@ Assert
            exists t b,
              cand_t == cand_t@pre && cand_base == cand_base@pre && n == n@pre &&
              0 <= n@pre && n@pre <= 200000 &&
              0 <= root && root <= n@pre / 2 - 1 && root <= n@pre - 1 &&
              Zlength(t) == n@pre && Zlength(b) == n@pre &&
          (forall q, (0 <= q && q < n@pre) =>
            (tlo <= t[q] && t[q] <= thi && blo <= b[q] && b[q] <= bhi)) &&
              ZipPerm(t0, b0, t, b) &&
              HeapOrderedFrom(t, n@pre - 1 + 1, root + 1) &&
              Int64Array::full(cand_t, n@pre, t) *
              Int64Array::full(cand_base, n@pre, b)
         */
        sift_candidates(cand_t, cand_base, root, n - 1)
        /*@ where cap = n@pre, tlo = tlo, thi = thi, blo = blo, bhi = bhi */;
    /*@ Assert
        exists t b,
          cand_t == cand_t@pre && cand_base == cand_base@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 200000 &&
          Zlength(t) == n@pre && Zlength(b) == n@pre &&
          (forall q, (0 <= q && q < n@pre) =>
            (tlo <= t[q] && t[q] <= thi && blo <= b[q] && b[q] <= bhi)) &&
          ZipPerm(t0, b0, t, b) &&
          HeapOrdered(t, n@pre) &&
          HeapSortState(t, n@pre, n@pre - 1) &&
          Int64Array::full(cand_t, n@pre, t) *
          Int64Array::full(cand_base, n@pre, b)
     */
    /*@ Inv Assert
        exists t b,
          cand_t == cand_t@pre && cand_base == cand_base@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 200000 &&
          -1 <= hi && hi <= n@pre - 1 &&
          Zlength(t) == n@pre && Zlength(b) == n@pre &&
          (forall q, (0 <= q && q < n@pre) =>
            (tlo <= t[q] && t[q] <= thi && blo <= b[q] && b[q] <= bhi)) &&
          ZipPerm(t0, b0, t, b) &&
          HeapOrdered(t, hi + 1) &&
          HeapSortState(t, n@pre, hi) &&
          Int64Array::full(cand_t, n@pre, t) *
          Int64Array::full(cand_base, n@pre, b)
     */
    for (int hi = n - 1; hi > 0; hi--) {
        long long v = cand_t[0]; cand_t[0] = cand_t[hi]; cand_t[hi] = v;
        v = cand_base[0]; cand_base[0] = cand_base[hi]; cand_base[hi] = v;
        /*@ Assert
            exists t b,
              cand_t == cand_t@pre && cand_base == cand_base@pre && n == n@pre &&
              0 <= n@pre && n@pre <= 200000 &&
              1 <= hi && hi <= n@pre - 1 &&
              v == b[hi] &&
              Zlength(t) == n@pre && Zlength(b) == n@pre &&
          (forall q, (0 <= q && q < n@pre) =>
            (tlo <= t[q] && t[q] <= thi && blo <= b[q] && b[q] <= bhi)) &&
              ZipPerm(t0, b0, t, b) &&
              HeapOrderedFrom(t, hi - 1 + 1, 0 + 1) &&
              HeapSortState(t, n@pre, hi - 1) &&
              Int64Array::full(cand_t, n@pre, t) *
              Int64Array::full(cand_base, n@pre, b)
         */
        sift_candidates(cand_t, cand_base, 0, hi - 1)
        /*@ where cap = n@pre, tlo = tlo, thi = thi, blo = blo, bhi = bhi */;
    }
}

/* solver: minimum minutes so that k users share a contribution. */
static long long solver(const long long *values, int n, int k, long long b,
                        long long c, long long *shifted,
                        long long *cand_t, long long *cand_base,
                        long long *heap)
/* QCP_INSERT_BEGIN:shard09-P086-normalized-solver-contract */
/*@ With (contributions : list Z)
    Require
      2 <= k && k <= Zlength(contributions) && 1 <= b && b <= 1000 && 1 <= c && c <= 1000 &&
      k <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (-1000000000 <= contributions[i] && contributions[i] <= 1000000000)) && n == Zlength(contributions) && Int64Array::full(values, n, contributions) * Int64Array::full_shape(shifted, n) * Int64Array::full_shape(cand_t, n) * Int64Array::full_shape(cand_base, n) * Int64Array::full_shape(heap, n)
    Ensure
      Spec(k, b, c, contributions, __return) && Int64Array::full(values, n, contributions) * Int64Array::full_shape(shifted, n) * Int64Array::full_shape(cand_t, n) * Int64Array::full_shape(cand_base, n) * Int64Array::full_shape(heap, n)
*/
/* QCP_INSERT_END:shard09-P086-normalized-solver-contract */
{
    long long W = b < 5 * c ? b : 5 * c;
    long long best = -1;
    /*@ Inv Assert
        exists sh ct cb hl,
          values == values@pre && n == n@pre && k == k@pre &&
          b == b@pre && c == c@pre && shifted == shifted@pre &&
          cand_t == cand_t@pre && cand_base == cand_base@pre &&
          heap == heap@pre &&
          2 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
          n@pre == Zlength(contributions) &&
          1 <= b@pre && b@pre <= 1000 && 1 <= c@pre && c@pre <= 1000 &&
          (forall q, (0 <= q && q < n@pre) =>
            (-1000000000 <= contributions[q] && contributions[q] <= 1000000000)) &&
          W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
          best == -1 &&
          0 <= i && i <= n@pre &&
          Zlength(sh) == n@pre && Zlength(ct) == n@pre &&
          Zlength(cb) == n@pre && Zlength(hl) == n@pre &&
          ShiftedPrefix(contributions, sh, i) &&
          Int64Array::full(values, n@pre, contributions) *
          Int64Array::full(shifted, n@pre, sh) *
          Int64Array::full(cand_t, n@pre, ct) *
          Int64Array::full(cand_base, n@pre, cb) *
          Int64Array::full(heap, n@pre, hl)
     */
    for (int i = 0; i < n; i++)
        shifted[i] = values[i] + SHIFT;
    /*@ Inv Assert
        exists sh ct cb hl,
          values == values@pre && n == n@pre && k == k@pre &&
          b == b@pre && c == c@pre && shifted == shifted@pre &&
          cand_t == cand_t@pre && cand_base == cand_base@pre &&
          heap == heap@pre &&
          2 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
          n@pre == Zlength(contributions) &&
          1 <= b@pre && b@pre <= 1000 && 1 <= c@pre && c@pre <= 1000 &&
          (forall q, (0 <= q && q < n@pre) =>
            (-1000000000 <= contributions[q] && contributions[q] <= 1000000000)) &&
          W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
          0 <= j && j <= 5 &&
          (best == -1 || (0 <= best && best <= 300000000000000000)) &&
          Zlength(sh) == n@pre && Zlength(ct) == n@pre &&
          Zlength(cb) == n@pre && Zlength(hl) == n@pre &&
          ShiftedPrefix(contributions, sh, n@pre) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= sh[q] && sh[q] <= 3000000000)) &&
          ResidueBest(contributions, k@pre, b@pre, c@pre, j, best) &&
          Int64Array::full(values, n@pre, contributions) *
          Int64Array::full(shifted, n@pre, sh) *
          Int64Array::full(cand_t, n@pre, ct) *
          Int64Array::full(cand_base, n@pre, cb) *
          Int64Array::full(heap, n@pre, hl)
     */
    for (int j = 0; j < 5; j++) {
        /*@ Inv Assert
            exists sh ct cb hl,
          values == values@pre && n == n@pre && k == k@pre &&
          b == b@pre && c == c@pre && shifted == shifted@pre &&
          cand_t == cand_t@pre && cand_base == cand_base@pre &&
          heap == heap@pre &&
          2 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
          n@pre == Zlength(contributions) &&
          1 <= b@pre && b@pre <= 1000 && 1 <= c@pre && c@pre <= 1000 &&
          (forall q, (0 <= q && q < n@pre) =>
            (-1000000000 <= contributions[q] && contributions[q] <= 1000000000)) &&
          W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
              0 <= j && j < 5 &&
          (best == -1 || (0 <= best && best <= 300000000000000000)) &&
              0 <= i && i <= n@pre &&
              Zlength(sh) == n@pre && Zlength(ct) == n@pre &&
              Zlength(cb) == n@pre && Zlength(hl) == n@pre &&
              ShiftedPrefix(contributions, sh, n@pre) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= sh[q] && sh[q] <= 3000000000)) &&
              CandPrefix(sh, j, W, c@pre, i, ct, cb) &&
              (forall q, (0 <= q && q < i) =>
                (1000000000 <= ct[q] && ct[q] <= 3000000004 &&
                 -600000000000 <= cb[q] && cb[q] <= 4000)) &&
              ResidueBest(contributions, k@pre, b@pre, c@pre, j, best) &&
              Int64Array::full(values, n@pre, contributions) *
              Int64Array::full(shifted, n@pre, sh) *
              Int64Array::full(cand_t, n@pre, ct) *
              Int64Array::full(cand_base, n@pre, cb) *
              Int64Array::full(heap, n@pre, hl)
         */
        for (int i = 0; i < n; i++) {
            long long rem = ((j - shifted[i]) % 5 + 5) % 5;
            long long tp = shifted[i] + rem; /* raised to target residue */
            cand_t[i] = tp;
            cand_base[i] = rem * c - (tp - j) / 5 * W;
        }
        sort_candidates(cand_t, cand_base, n)
        /*@ where tlo = 1000000000, thi = 3000000004,
                  blo = -600000000000, bhi = 4000 */;
        /*@ Assert
            exists sh ct cb st sb hl,
          values == values@pre && n == n@pre && k == k@pre &&
          b == b@pre && c == c@pre && shifted == shifted@pre &&
          cand_t == cand_t@pre && cand_base == cand_base@pre &&
          heap == heap@pre &&
          2 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
          n@pre == Zlength(contributions) &&
          1 <= b@pre && b@pre <= 1000 && 1 <= c@pre && c@pre <= 1000 &&
          (forall q, (0 <= q && q < n@pre) =>
            (-1000000000 <= contributions[q] && contributions[q] <= 1000000000)) &&
          W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
              0 <= j && j < 5 &&
          (best == -1 || (0 <= best && best <= 300000000000000000)) &&
              Zlength(sh) == n@pre && Zlength(ct) == n@pre &&
              Zlength(cb) == n@pre && Zlength(hl) == n@pre &&
              Zlength(st) == n@pre && Zlength(sb) == n@pre &&
              ShiftedPrefix(contributions, sh, n@pre) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= sh[q] && sh[q] <= 3000000000)) &&
              CandPrefix(sh, j, W, c@pre, n@pre, ct, cb) &&
              ZipPerm(ct, cb, st, sb) &&
              Nondecreasing(st) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= st[q] && st[q] <= 3000000004 &&
             -600000000000 <= sb[q] && sb[q] <= 4000)) &&
              ResidueBest(contributions, k@pre, b@pre, c@pre, j, best) &&
              Int64Array::full(values, n@pre, contributions) *
              Int64Array::full(shifted, n@pre, sh) *
              Int64Array::full(cand_t, n@pre, st) *
              Int64Array::full(cand_base, n@pre, sb) *
              Int64Array::full(heap, n@pre, hl)
         */
        int hsize = 0;
        long long hsum = 0;
        /*@ Inv Assert
            exists sh ct cb st sb hl,
          values == values@pre && n == n@pre && k == k@pre &&
          b == b@pre && c == c@pre && shifted == shifted@pre &&
          cand_t == cand_t@pre && cand_base == cand_base@pre &&
          heap == heap@pre &&
          2 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
          n@pre == Zlength(contributions) &&
          1 <= b@pre && b@pre <= 1000 && 1 <= c@pre && c@pre <= 1000 &&
          (forall q, (0 <= q && q < n@pre) =>
            (-1000000000 <= contributions[q] && contributions[q] <= 1000000000)) &&
          W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
              0 <= j && j < 5 &&
          (best == -1 || (0 <= best && best <= 300000000000000000)) &&
              0 <= i && i <= n@pre &&
              0 <= hsize &&
              ((i <= k@pre && hsize == i) || (k@pre < i && hsize == k@pre)) &&
              -300000000000000000 <= hsum && hsum <= 300000000000000000 &&
              Zlength(sh) == n@pre && Zlength(ct) == n@pre &&
              Zlength(cb) == n@pre && Zlength(hl) == n@pre &&
              Zlength(st) == n@pre && Zlength(sb) == n@pre &&
              ShiftedPrefix(contributions, sh, n@pre) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= sh[q] && sh[q] <= 3000000000)) &&
              CandPrefix(sh, j, W, c@pre, n@pre, ct, cb) &&
              ZipPerm(ct, cb, st, sb) &&
              Nondecreasing(st) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= st[q] && st[q] <= 3000000004 &&
             -600000000000 <= sb[q] && sb[q] <= 4000)) &&
              (forall q, (0 <= q && q < hsize) =>
                (-600000000000 <= hl[q] && hl[q] <= 4000)) &&
              HeapOrdered(hl, hsize) &&
              hsum == ZSum(sublist(0, hsize, hl)) &&
              HeapContent(sb, i, sublist(0, hsize, hl), hsum) &&
              SweepBest(contributions, k@pre, b@pre, c@pre, j, st, sb, W, i, best) &&
              Int64Array::full(values, n@pre, contributions) *
              Int64Array::full(shifted, n@pre, sh) *
              Int64Array::full(cand_t, n@pre, st) *
              Int64Array::full(cand_base, n@pre, sb) *
              Int64Array::full(heap, n@pre, hl)
         */
        for (int i = 0; i < n; i++) {
            hpush(heap, &hsize, &hsum, cand_base[i])
            /*@ where cap = n@pre */;
            if (hsize > k)
                hpop(heap, &hsize, &hsum)
                /*@ where cap = n@pre */;
            /*@ Assert
                exists sh ct cb st sb hl,
          values == values@pre && n == n@pre && k == k@pre &&
          b == b@pre && c == c@pre && shifted == shifted@pre &&
          cand_t == cand_t@pre && cand_base == cand_base@pre &&
          heap == heap@pre &&
          2 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
          n@pre == Zlength(contributions) &&
          1 <= b@pre && b@pre <= 1000 && 1 <= c@pre && c@pre <= 1000 &&
          (forall q, (0 <= q && q < n@pre) =>
            (-1000000000 <= contributions[q] && contributions[q] <= 1000000000)) &&
          W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
                  0 <= j && j < 5 &&
          (best == -1 || (0 <= best && best <= 300000000000000000)) &&
                  0 <= i && i < n@pre &&
                  0 <= hsize &&
                  ((i + 1 <= k@pre && hsize == i + 1) ||
                   (k@pre < i + 1 && hsize == k@pre)) &&
                  -300000000000000000 <= hsum && hsum <= 300000000000000000 &&
                  Zlength(sh) == n@pre && Zlength(ct) == n@pre &&
                  Zlength(cb) == n@pre && Zlength(hl) == n@pre &&
                  Zlength(st) == n@pre && Zlength(sb) == n@pre &&
                  ShiftedPrefix(contributions, sh, n@pre) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= sh[q] && sh[q] <= 3000000000)) &&
                  CandPrefix(sh, j, W, c@pre, n@pre, ct, cb) &&
                  ZipPerm(ct, cb, st, sb) &&
                  Nondecreasing(st) &&
          (forall q, (0 <= q && q < n@pre) =>
            (1000000000 <= st[q] && st[q] <= 3000000004 &&
             -600000000000 <= sb[q] && sb[q] <= 4000)) &&
                  (forall q, (0 <= q && q < hsize) =>
                    (-600000000000 <= hl[q] && hl[q] <= 4000)) &&
                  HeapOrdered(hl, hsize) &&
                  hsum == ZSum(sublist(0, hsize, hl)) &&
                  HeapContent(sb, i + 1, sublist(0, hsize, hl), hsum) &&
                  SweepBest(contributions, k@pre, b@pre, c@pre, j, st, sb, W, i, best) &&
                  Int64Array::full(values, n@pre, contributions) *
                  Int64Array::full(shifted, n@pre, sh) *
                  Int64Array::full(cand_t, n@pre, st) *
                  Int64Array::full(cand_base, n@pre, sb) *
                  Int64Array::full(heap, n@pre, hl)
             */
            if (hsize == k) {
                long long total = hsum + (long long)k * ((cand_t[i] - j) / 5) * W;
                /*@ Assert
                    exists sh ct cb st sb hl,
                      values == values@pre && n == n@pre && k == k@pre &&
                      b == b@pre && c == c@pre && shifted == shifted@pre &&
                      cand_t == cand_t@pre && cand_base == cand_base@pre &&
                      heap == heap@pre &&
                      2 <= k@pre && k@pre <= n@pre && n@pre <= 200000 &&
                      n@pre == Zlength(contributions) &&
                      1 <= b@pre && b@pre <= 1000 && 1 <= c@pre && c@pre <= 1000 &&
                      (forall q, (0 <= q && q < n@pre) =>
                        (-1000000000 <= contributions[q] &&
                         contributions[q] <= 1000000000)) &&
                      W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
                      0 <= j && j < 5 &&
                      (best == -1 || (0 <= best && best <= 300000000000000000)) &&
                      0 <= i && i < n@pre &&
                      hsize == k@pre && k@pre - 1 <= i &&
                      -300000000000000000 <= hsum && hsum <= 300000000000000000 &&
                      0 <= total && total <= 300000000000000000 &&
                      total == hsum + k@pre * ((st[i] - j) / 5) * W &&
                      Zlength(sh) == n@pre && Zlength(ct) == n@pre &&
                      Zlength(cb) == n@pre && Zlength(hl) == n@pre &&
                      Zlength(st) == n@pre && Zlength(sb) == n@pre &&
                      ShiftedPrefix(contributions, sh, n@pre) &&
                      (forall q, (0 <= q && q < n@pre) =>
                        (1000000000 <= sh[q] && sh[q] <= 3000000000)) &&
                      CandPrefix(sh, j, W, c@pre, n@pre, ct, cb) &&
                      ZipPerm(ct, cb, st, sb) &&
                      Nondecreasing(st) &&
                      (forall q, (0 <= q && q < n@pre) =>
                        (1000000000 <= st[q] && st[q] <= 3000000004 &&
                         -600000000000 <= sb[q] && sb[q] <= 4000)) &&
                      (forall q, (0 <= q && q < hsize) =>
                        (-600000000000 <= hl[q] && hl[q] <= 4000)) &&
                      HeapOrdered(hl, hsize) &&
                      hsum == ZSum(sublist(0, hsize, hl)) &&
                      HeapContent(sb, i + 1, sublist(0, hsize, hl), hsum) &&
                      KSmallSum(sublist(0, i + 1, sb), k@pre, hsum) &&
                      SweepValue(st, sb, k@pre, j, W, i, total) &&
                      TieCostAtResidue(contributions, k@pre, b@pre, c@pre, j, total) &&
                      SweepBest(contributions, k@pre, b@pre, c@pre, j, st, sb, W, i, best) &&
                      Int64Array::full(values, n@pre, contributions) *
                      Int64Array::full(shifted, n@pre, sh) *
                      Int64Array::full(cand_t, n@pre, st) *
                      Int64Array::full(cand_base, n@pre, sb) *
                      Int64Array::full(heap, n@pre, hl)
                 */
                if (best < 0 || total < best)
                    best = total;
            }
        }
    }
    /*@ Assert
        values == values@pre && n == n@pre && k == k@pre &&
        b == b@pre && c == c@pre && shifted == shifted@pre &&
        cand_t == cand_t@pre && cand_base == cand_base@pre &&
        heap == heap@pre &&
        W == WCost(b@pre, c@pre) && 1 <= W && W <= 1000 &&
        Spec(k@pre, b@pre, c@pre, contributions, best) &&
        Int64Array::full(values, n@pre, contributions) *
        Int64Array::full_shape(shifted, n@pre) *
        Int64Array::full_shape(cand_t, n@pre) *
        Int64Array::full_shape(cand_base, n@pre) *
        Int64Array::full_shape(heap, n@pre)
     */
    return best;
}

// int main(void)
// {
//     int n, k;
//     long long b, c;
//     if (scanf("%d %d %lld %lld", &n, &k, &b, &c) != 4)
//         return 0;
//     static long long values[200005], shifted[200005];
//     static long long cand_t[200005], cand_base[200005], heap[200005];
//     for (int i = 0; i < n; i++) {
//         long long v;
//         scanf("%lld", &v);
//         values[i] = v;
//     }
//     printf("%lld\n", solver(values, n, k, b, c, shifted,
//                             cand_t, cand_base, heap));
//     return 0;
// }
