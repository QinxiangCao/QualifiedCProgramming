/*
 * Codeforces 946/G - Almost Increasing Array  (rating 2500, DP)
 *
 * Replacements are unconstrained, so the elements we keep are exactly a
 * subsequence that may stay: with c_i = a_i - i, "strictly increasing" means
 * the kept c's are non-decreasing (there is always room to fill the gaps).
 * Deleting one element shifts every later index by one, adding 1 to their c.
 * So keep as many as possible with a BIT-accelerated longest non-decreasing
 * subsequence in two layers — before the deletion (value c_i) and after it
 * (value c_i + 1) — where entering the second layer must skip a real position.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P089-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P089-solver-support */

/*@ Extern Coq
      (MemberPrefix : list Z -> Z -> Z -> Prop)
      (StrictIncPrefix : list Z -> Z -> Prop)
      (RankResult : list Z -> Z -> Z -> Z -> Prop)
      (RangeMax : list Z -> Z -> Z -> Z)
      (MaxBitRep : list Z -> list Z -> Z -> Prop)
      (MaxBitInsert : list Z -> Z -> Z -> list Z)
*/

/*@ Extern Coq
      (KeyPrefix : list Z -> list Z -> Z -> Prop)
      (ValsRawPrefix : list Z -> list Z -> Z -> Prop)
      (DedupState : list Z -> list Z -> Z -> Z -> Prop)
      (CompressedKeys : list Z -> list Z -> Z -> Prop)
      (DP0Prefix : list Z -> list Z -> Z -> Prop)
      (ClampedPrefixMax : list Z -> Z -> Z -> Prop)
      (ClampedBest1Upto : list Z -> Z -> Z -> Prop)
      (Bit0Model : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (Bit1Model : list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (MaxBitAddProgress : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (MaxBitQueryState : list Z -> Z -> Z -> Z -> Prop)
      (RankSearchState : list Z -> Z -> Z -> Z -> Prop)
*/

#define MAXN 200005
// #define NEG (-1000000000)

static void upd(int *bit, int nvals, int i, int v)
/*@ With (total : Z) (bit_l : list Z) (m : list Z)
    Require
      1 <= nvals && nvals + 1 <= total && total <= 400001 &&
      1 <= i && i <= nvals &&
      -1000000000 <= v && v <= 1000000000 &&
      Zlength(bit_l) == total &&
      (forall k, (0 <= k && k < total) =>
         (-1000000000 <= bit_l[k] && bit_l[k] <= 1000000000)) &&
      MaxBitRep(m, bit_l, nvals) &&
      IntArray::full(bit, total, bit_l)
    Ensure
      exists (bit_l1 : list Z),
        Zlength(bit_l1) == total &&
        (forall k, (0 <= k && k < total) =>
           (-1000000000 <= bit_l1[k] && bit_l1[k] <= 1000000000)) &&
        MaxBitRep(MaxBitInsert(m, i@pre, v@pre), bit_l1, nvals@pre) &&
        IntArray::full(bit@pre, total, bit_l1)
*/
{
    /*@ Inv Assert
        exists (bit_cur : list Z),
          bit == bit@pre && nvals == nvals@pre && v == v@pre &&
          1 <= nvals@pre && nvals@pre + 1 <= total && total <= 400001 &&
          1 <= i@pre && i@pre <= nvals@pre &&
          -1000000000 <= v@pre && v@pre <= 1000000000 &&
          i@pre <= i && i <= 2 * nvals@pre &&
          Zlength(bit_cur) == total &&
          (forall k, (0 <= k && k < total) =>
             (-1000000000 <= bit_cur[k] && bit_cur[k] <= 1000000000)) &&
          MaxBitRep(m, bit_l, nvals@pre) &&
          MaxBitAddProgress(bit_l, bit_cur, nvals@pre, i@pre, i, v@pre) &&
          IntArray::full(bit@pre, total, bit_cur)
    */
    for (; i <= nvals; i += i & (-i))
        if (bit[i] < v)
            bit[i] = v;
}

static int qry(const int *bit, int i)
/*@ With (total : Z) (nvals : Z) (bit_l : list Z) (m : list Z)
    Require
      1 <= nvals && nvals + 1 <= total && total <= 400001 &&
      0 <= i && i <= nvals &&
      Zlength(bit_l) == total &&
      (forall k, (0 <= k && k < total) =>
         (-1000000000 <= bit_l[k] && bit_l[k] <= 1000000000)) &&
      MaxBitRep(m, bit_l, nvals) &&
      IntArray::full(bit, total, bit_l)
    Ensure
      __return == RangeMax(m, 1, i@pre + 1) &&
      -1000000000 <= __return && __return <= 1000000000 &&
      IntArray::full(bit@pre, total, bit_l)
*/
{
    int r = (-1000000000);
    /*@ Inv Assert
          bit == bit@pre &&
          1 <= nvals && nvals + 1 <= total && total <= 400001 &&
          0 <= i && i <= i@pre && i@pre <= nvals &&
          Zlength(bit_l) == total &&
          (forall k, (0 <= k && k < total) =>
             (-1000000000 <= bit_l[k] && bit_l[k] <= 1000000000)) &&
          -1000000000 <= r && r <= 1000000000 &&
          MaxBitRep(m, bit_l, nvals) &&
          MaxBitQueryState(m, i@pre, i, r) &&
          IntArray::full(bit@pre, total, bit_l)
    */
    for (; i > 0; i -= i & (-i))
        if (bit[i] > r)
            r = bit[i];
    return r;
}

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

static int rank_of(long long v, const int *vals, int nvals)
/*@ With (total : Z) (vals_l : list Z)
    Require
      1 <= nvals && nvals <= total && total <= 400000 &&
      Zlength(vals_l) == total &&
      -2000000000 <= v && v <= 2000000000 &&
      StrictIncPrefix(vals_l, nvals) &&
      MemberPrefix(vals_l, nvals, v) &&
      (forall k, (0 <= k && k < total) =>
         (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
      IntArray::full(vals, total, vals_l)
    Ensure
      RankResult(vals_l, nvals@pre, v@pre, __return) &&
      1 <= __return && __return <= nvals@pre &&
      IntArray::full(vals@pre, total, vals_l)
*/
{
    int lo = 0, hi = nvals - 1;
    /*@ Inv Assert
          vals == vals@pre && nvals == nvals@pre && v == v@pre &&
          1 <= nvals@pre && nvals@pre <= total && total <= 400000 &&
          Zlength(vals_l) == total &&
          -2000000000 <= v@pre && v@pre <= 2000000000 &&
          (forall k, (0 <= k && k < total) =>
             (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
          StrictIncPrefix(vals_l, nvals@pre) &&
          MemberPrefix(vals_l, nvals@pre, v@pre) &&
          0 <= lo && lo <= hi && hi <= nvals@pre - 1 &&
          RankSearchState(vals_l, v@pre, lo, hi) &&
          IntArray::full(vals@pre, total, vals_l)
    */
    while (lo < hi) {
        int mid = (lo + hi) / 2;
        /*@ Assert
              vals == vals@pre && nvals == nvals@pre && v == v@pre &&
              1 <= nvals@pre && nvals@pre <= total && total <= 400000 &&
              Zlength(vals_l) == total &&
              -2000000000 <= v@pre && v@pre <= 2000000000 &&
              (forall k, (0 <= k && k < total) =>
                 (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
              StrictIncPrefix(vals_l, nvals@pre) &&
              MemberPrefix(vals_l, nvals@pre, v@pre) &&
              0 <= lo && lo <= mid && mid < hi && hi <= nvals@pre - 1 &&
              RankSearchState(vals_l, v@pre, lo, hi) &&
              IntArray::full(vals@pre, total, vals_l)
        */
        if (vals[mid] < v)
            lo = mid + 1;
        else
            hi = mid;
    }
    return lo + 1;
}

/* solver: minimum number of replacements. */
static int solver(const int *a, int n, long long *c, int *dp0,
                  int *vals, int *bit0, int *bit1, int *bitX)
/* QCP_INSERT_BEGIN:shard09-P089-normalized-solver-contract */
/*@ With (values : list Z)
    Require
      2 <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 1000000000)) && n == Zlength(values) && IntArray::full(a, n, values) * Int64Array::full_shape(c, n) * IntArray::full_shape(dp0, n) * IntArray::full_shape(vals, 2 * n) * IntArray::full_shape(bit0, 2 * n + 1) * IntArray::full_shape(bit1, 2 * n + 1) * IntArray::full_shape(bitX, 2 * n + 1)
    Ensure
      Spec(values, __return) && IntArray::full(a, n, values) * Int64Array::full_shape(c, n) * IntArray::full_shape(dp0, n) * IntArray::full_shape(vals, 2 * n) * IntArray::full_shape(bit0, 2 * n + 1) * IntArray::full_shape(bit1, 2 * n + 1) * IntArray::full_shape(bitX, 2 * n + 1)
*/
/* QCP_INSERT_END:shard09-P089-normalized-solver-contract */
{
    /*@ Inv Assert
        exists (c_l : list Z),
          a == a@pre && n == n@pre && c == c@pre && dp0 == dp0@pre &&
          vals == vals@pre && bit0 == bit0@pre && bit1 == bit1@pre &&
          bitX == bitX@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= values[q] && values[q] <= 1000000000)) &&
          0 <= i && i <= n@pre && Zlength(c_l) == n@pre &&
          KeyPrefix(values, c_l, i) &&
          (forall k, (0 <= k && k < i) =>
             (1 - n@pre <= c_l[k] && c_l[k] <= 1000000000)) &&
          IntArray::full(a@pre, n@pre, values) *
          Int64Array::full(c@pre, n@pre, c_l) *
          IntArray::full_shape(dp0@pre, n@pre) *
          IntArray::full_shape(vals@pre, 2 * n@pre) *
          IntArray::full_shape(bit0@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bit1@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bitX@pre, 2 * n@pre + 1)
    */
    for (int i = 0; i < n; i++)
        c[i] = (long long)a[i] - i;
    int nvals = 0;
    /*@ Inv Assert
        exists (c_l : list Z) (vals_l : list Z),
          a == a@pre && n == n@pre && c == c@pre && dp0 == dp0@pre &&
          vals == vals@pre && bit0 == bit0@pre && bit1 == bit1@pre &&
          bitX == bitX@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= values[q] && values[q] <= 1000000000)) &&
          0 <= i && i <= n@pre && nvals == 2 * i &&
          Zlength(c_l) == n@pre && Zlength(vals_l) == 2 * n@pre &&
          KeyPrefix(values, c_l, n@pre) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 - n@pre <= c_l[k] && c_l[k] <= 1000000000)) &&
          ValsRawPrefix(values, vals_l, i) &&
          (forall k, (0 <= k && k < 2 * i) =>
             (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
          IntArray::full(a@pre, n@pre, values) *
          Int64Array::full(c@pre, n@pre, c_l) *
          IntArray::full(vals@pre, 2 * n@pre, vals_l) *
          IntArray::full_shape(dp0@pre, n@pre) *
          IntArray::full_shape(bit0@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bit1@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bitX@pre, 2 * n@pre + 1)
    */
    for (int i = 0; i < n; i++) {
        { vals[nvals] = (int)c[i]; nvals++; }
        { vals[nvals] = (int)c[i] + 1; nvals++; }
    }
    // qsort(vals, nvals, sizeof *vals, cmp_int);
    /*@ Assert
        exists (c_l : list Z) (vals_l : list Z),
          a == a@pre && n == n@pre && c == c@pre && dp0 == dp0@pre &&
          vals == vals@pre && bit0 == bit0@pre && bit1 == bit1@pre &&
          bitX == bitX@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= values[q] && values[q] <= 1000000000)) &&
          nvals == 2 * n@pre &&
          Zlength(c_l) == n@pre && Zlength(vals_l) == 2 * n@pre &&
          KeyPrefix(values, c_l, n@pre) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 - n@pre <= c_l[k] && c_l[k] <= 1000000000)) &&
          ValsRawPrefix(values, vals_l, n@pre) &&
          (forall k, (0 <= k && k < 2 * n@pre) =>
             (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
          IntArray::full(a@pre, n@pre, values) *
          Int64Array::full(c@pre, n@pre, c_l) *
          IntArray::full(vals@pre, 2 * n@pre, vals_l) *
          IntArray::full_shape(dp0@pre, n@pre) *
          IntArray::full_shape(bit0@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bit1@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bitX@pre, 2 * n@pre + 1)
    */
    quicksort(vals, nvals);
    int uniq = 0;
    /*@ Inv Assert
        exists (c_l : list Z) (raw_l : list Z) (sorted_l : list Z)
               (cur_l : list Z),
          a == a@pre && n == n@pre && c == c@pre && dp0 == dp0@pre &&
          vals == vals@pre && bit0 == bit0@pre && bit1 == bit1@pre &&
          bitX == bitX@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= values[q] && values[q] <= 1000000000)) &&
          nvals == 2 * n@pre &&
          Zlength(c_l) == n@pre && Zlength(raw_l) == 2 * n@pre &&
          Zlength(sorted_l) == 2 * n@pre && Zlength(cur_l) == 2 * n@pre &&
          KeyPrefix(values, c_l, n@pre) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 - n@pre <= c_l[k] && c_l[k] <= 1000000000)) &&
          ValsRawPrefix(values, raw_l, n@pre) &&
          Permutation(raw_l, sorted_l) && mono_nondec(sorted_l) &&
          (forall k, (0 <= k && k < 2 * n@pre) =>
             (-2000000000 <= sorted_l[k] && sorted_l[k] <= 2000000000)) &&
          (forall k, (0 <= k && k < 2 * n@pre) =>
             (-2000000000 <= cur_l[k] && cur_l[k] <= 2000000000)) &&
          0 <= uniq && uniq <= i && i <= 2 * n@pre &&
          (forall p, (uniq <= p && p < 2 * n@pre) => cur_l[p] == sorted_l[p]) &&
          DedupState(sorted_l, cur_l, uniq, i) &&
          IntArray::full(a@pre, n@pre, values) *
          Int64Array::full(c@pre, n@pre, c_l) *
          IntArray::full(vals@pre, 2 * n@pre, cur_l) *
          IntArray::full_shape(dp0@pre, n@pre) *
          IntArray::full_shape(bit0@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bit1@pre, 2 * n@pre + 1) *
          IntArray::full_shape(bitX@pre, 2 * n@pre + 1)
    */
    for (int i = 0; i < nvals; i++)
        if (i == 0 || vals[i] != vals[i - 1])
            { vals[uniq] = vals[i]; uniq++; }
    nvals = uniq;
    /*@ Assert
        exists (c_l : list Z) (vals_l : list Z) (bit0_l : list Z)
               (bit1_l : list Z) (bitX_l : list Z),
          a == a@pre && n == n@pre && c == c@pre && dp0 == dp0@pre &&
          vals == vals@pre && bit0 == bit0@pre && bit1 == bit1@pre &&
          bitX == bitX@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= values[q] && values[q] <= 1000000000)) &&
          nvals == uniq && 1 <= nvals && nvals <= 2 * n@pre &&
          Zlength(c_l) == n@pre && Zlength(vals_l) == 2 * n@pre &&
          KeyPrefix(values, c_l, n@pre) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 - n@pre <= c_l[k] && c_l[k] <= 1000000000)) &&
          (forall k, (0 <= k && k < 2 * n@pre) =>
             (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
          CompressedKeys(values, vals_l, nvals) &&
          Zlength(bit0_l) == nvals + 1 && Zlength(bit1_l) == nvals + 1 &&
          Zlength(bitX_l) == nvals + 1 &&
          IntArray::full(a@pre, n@pre, values) *
          Int64Array::full(c@pre, n@pre, c_l) *
          IntArray::full(vals@pre, 2 * n@pre, vals_l) *
          IntArray::full_shape(dp0@pre, n@pre) *
          IntArray::full(bit0@pre, nvals + 1, bit0_l) *
          IntArray::seg_shape(bit0@pre, nvals + 1, 2 * n@pre + 1) *
          IntArray::full(bit1@pre, nvals + 1, bit1_l) *
          IntArray::seg_shape(bit1@pre, nvals + 1, 2 * n@pre + 1) *
          IntArray::full(bitX@pre, nvals + 1, bitX_l) *
          IntArray::seg_shape(bitX@pre, nvals + 1, 2 * n@pre + 1)
    */
    /*@ Inv Assert
        exists (c_l : list Z) (vals_l : list Z) (bit0_l : list Z)
               (bit1_l : list Z) (bitX_l : list Z),
          a == a@pre && n == n@pre && c == c@pre && dp0 == dp0@pre &&
          vals == vals@pre && bit0 == bit0@pre && bit1 == bit1@pre &&
          bitX == bitX@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= values[q] && values[q] <= 1000000000)) &&
          nvals == uniq && 1 <= nvals && nvals <= 2 * n@pre &&
          0 <= i && i <= nvals + 1 &&
          Zlength(c_l) == n@pre && Zlength(vals_l) == 2 * n@pre &&
          KeyPrefix(values, c_l, n@pre) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 - n@pre <= c_l[k] && c_l[k] <= 1000000000)) &&
          (forall k, (0 <= k && k < 2 * n@pre) =>
             (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
          CompressedKeys(values, vals_l, nvals) &&
          Zlength(bit0_l) == nvals + 1 && Zlength(bit1_l) == nvals + 1 &&
          Zlength(bitX_l) == nvals + 1 &&
          (forall k, (0 <= k && k < i) =>
             (bit0_l[k] == -1000000000 && bit1_l[k] == -1000000000 &&
              bitX_l[k] == -1000000000)) &&
          IntArray::full(a@pre, n@pre, values) *
          Int64Array::full(c@pre, n@pre, c_l) *
          IntArray::full(vals@pre, 2 * n@pre, vals_l) *
          IntArray::full_shape(dp0@pre, n@pre) *
          IntArray::full(bit0@pre, nvals + 1, bit0_l) *
          IntArray::seg_shape(bit0@pre, nvals + 1, 2 * n@pre + 1) *
          IntArray::full(bit1@pre, nvals + 1, bit1_l) *
          IntArray::seg_shape(bit1@pre, nvals + 1, 2 * n@pre + 1) *
          IntArray::full(bitX@pre, nvals + 1, bitX_l) *
          IntArray::seg_shape(bitX@pre, nvals + 1, 2 * n@pre + 1)
    */
    for (int i = 0; i <= nvals; i++){
        bitX[i] = (-1000000000);
        bit1[i] = bitX[i];
        bit0[i] = bit1[i];
    }

    int best0 = 0, best1 = 0, best0_prefix = 0;
    /*@ Inv Assert
        exists (c_l : list Z) (vals_l : list Z) (dp0_l : list Z)
               (bit0_l : list Z) (bit1_l : list Z) (bitX_l : list Z)
               (m0 : list Z) (m1 : list Z) (mX : list Z),
          a == a@pre && n == n@pre && c == c@pre && dp0 == dp0@pre &&
          vals == vals@pre && bit0 == bit0@pre && bit1 == bit1@pre &&
          bitX == bitX@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= values[q] && values[q] <= 1000000000)) &&
          nvals == uniq && 1 <= nvals && nvals <= 2 * n@pre &&
          0 <= i && i <= n@pre &&
          Zlength(c_l) == n@pre && Zlength(vals_l) == 2 * n@pre &&
          Zlength(dp0_l) == n@pre &&
          KeyPrefix(values, c_l, n@pre) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 - n@pre <= c_l[k] && c_l[k] <= 1000000000)) &&
          (forall k, (0 <= k && k < 2 * n@pre) =>
             (-2000000000 <= vals_l[k] && vals_l[k] <= 2000000000)) &&
          CompressedKeys(values, vals_l, nvals) &&
          (forall k, (0 <= k && k < nvals + 1) =>
             (-1000000000 <= bit0_l[k] && bit0_l[k] <= 1000000000 &&
              -1000000000 <= bit1_l[k] && bit1_l[k] <= 1000000000 &&
              -1000000000 <= bitX_l[k] && bitX_l[k] <= 1000000000)) &&
          Zlength(bit0_l) == nvals + 1 && Zlength(bit1_l) == nvals + 1 &&
          Zlength(bitX_l) == nvals + 1 &&
          MaxBitRep(m0, bit0_l, nvals) && MaxBitRep(m1, bit1_l, nvals) &&
          MaxBitRep(mX, bitX_l, nvals) &&
          (forall r, (0 <= r && r <= nvals) =>
             (-1000000000 <= m0[r] && m0[r] <= n@pre &&
              -1000000000 <= m1[r] && m1[r] <= n@pre &&
              -1000000000 <= mX[r] && mX[r] <= n@pre)) &&
          DP0Prefix(values, dp0_l, i) &&
          (forall k, (0 <= k && k < i) =>
             (1 <= dp0_l[k] && dp0_l[k] <= n@pre)) &&
          Bit0Model(values, vals_l, dp0_l, m0, i, nvals) &&
          Bit1Model(values, vals_l, m1, i, nvals) &&
          Bit0Model(values, vals_l, dp0_l, mX, i - 1, nvals) &&
          ClampedPrefixMax(dp0_l, i, best0) &&
          ClampedBest1Upto(values, i, best1) &&
          ClampedPrefixMax(dp0_l, i - 1, best0_prefix) &&
          0 <= best0 && best0 <= n@pre &&
          0 <= best1 && best1 <= n@pre &&
          0 <= best0_prefix && best0_prefix <= n@pre &&
          IntArray::full(a@pre, n@pre, values) *
          Int64Array::full(c@pre, n@pre, c_l) *
          IntArray::full(vals@pre, 2 * n@pre, vals_l) *
          IntArray::full(dp0@pre, n@pre, dp0_l) *
          IntArray::full(bit0@pre, nvals + 1, bit0_l) *
          IntArray::seg_shape(bit0@pre, nvals + 1, 2 * n@pre + 1) *
          IntArray::full(bit1@pre, nvals + 1, bit1_l) *
          IntArray::seg_shape(bit1@pre, nvals + 1, 2 * n@pre + 1) *
          IntArray::full(bitX@pre, nvals + 1, bitX_l) *
          IntArray::seg_shape(bitX@pre, nvals + 1, 2 * n@pre + 1)
    */
    for (int i = 0; i < n; i++) {
        int r0 = rank_of(c[i], vals, nvals) /*@ where total = 2 * n@pre */;
        int r1 = rank_of(c[i] + 1, vals, nvals) /*@ where total = 2 * n@pre */;
        int prev0 = qry(bit0, r0) /*@ where total = nvals + 1, nvals = nvals */;
        int d0 = (prev0 > 0 ? prev0 : 0) + 1;

        int d1 = (-1000000000);
        if (i >= 1) {                     /* something before i can be deleted */
            int best_prev = 0;            /* start fresh right after the gap */
            int viaSame = qry(bit1, r1) /*@ where total = nvals + 1, nvals = nvals */;
            if (viaSame > best_prev)
                best_prev = viaSame;
            int viaCross = qry(bitX, r1) /*@ where total = nvals + 1, nvals = nvals */;
            if (viaCross > best_prev)
                best_prev = viaCross;
            d1 = best_prev + 1;
        }

        dp0[i] = d0;
        if (d0 > best0) best0 = d0;
        if (d1 > best1) best1 = d1;
        upd(bit0, nvals, r0, d0) /*@ where total = nvals + 1 */;
        if (d1 > (-1000000000)) upd(bit1, nvals, r1, d1) /*@ where total = nvals + 1 */;
        if (i >= 1) {                     /* dp0[i-1] is now crossable */
            upd(bitX, nvals, rank_of(c[i - 1], vals, nvals) /*@ where total = 2 * n@pre */, dp0[i - 1])
                /*@ where total = nvals + 1 */;
            if (dp0[i - 1] > best0_prefix)
                best0_prefix = dp0[i - 1];
        }
    }
    int cost0 = n - best0;
    int keptDel = best1 > best0_prefix ? best1 : best0_prefix;
    int cost1 = n - 1 - keptDel;
    return cost0 < cost1 ? cost0 : cost1;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int a[MAXN], dp0[MAXN], vals[2 * MAXN];
//     static int bit0[2 * MAXN], bit1[2 * MAXN], bitX[2 * MAXN];
//     static long long c[MAXN];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%d\n", solver(a, n, c, dp0, vals, bit0, bit1, bitX));
//     return 0;
// }
