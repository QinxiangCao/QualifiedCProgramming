// #include <stdio.h>
// #include <stdlib.h>
typedef long long i64;
typedef struct
{
    int l, r;
} Seg;

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Permutation : list (Z * Z) -> list (Z * Z) -> Prop)
      (SegmentAllocationSize : Z -> Z -> Prop)
      (SegmentsProper : list (Z * Z) -> Prop)
      (SegmentsBounded : list (Z * Z) -> Prop)
      (SegmentsSortedByLeft : list (Z * Z) -> Prop)
      (SolverScanState : list Z -> list Z -> Z -> Z ->
                         list (Z * Z) -> list (Z * Z) -> Prop)
      (DirectedOverlapMaximumPrefix : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Prop)
      (DirectedOverlapMaximum : list (Z * Z) -> list (Z * Z) -> Z -> Prop)
      (PrefixRightMaxima : list (Z * Z) -> list Z -> Z -> Prop)
      (UpperBoundBracket : list (Z * Z) -> Z -> Z -> Z -> Prop)
      (SwappingOverlapMaximum : list Z -> list Z -> Z -> Prop)
      (PairDistanceSum : list Z -> list Z -> Z)
      (SegArray::full : Z -> Z -> list (Z * Z) -> Assertion)
      (SegArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P087_1513F_swapping_problem_lib */

void *malloc(unsigned long size)
/*@ malloc_seg
    With (capacity : Z)
    Require
      0 <= capacity && SegmentAllocationSize(size, capacity)
    Ensure
      __return != 0 && SegArray::undef_full(__return, capacity)
*/
/*@ malloc_int
    With (capacity : Z)
    Require
      0 <= capacity && size == capacity * sizeof(int)
    Ensure
      __return != 0 && IntArray::undef_full(__return, capacity)
*/;

void free(void *ptr)
/*@ free_int
    With (capacity : Z)
    Require
      exists values,
        Zlength(values) == capacity && IntArray::full(ptr, capacity, values)
    Ensure emp
*/
/*@ free_seg_mixed
    With (capacity : Z) (count : Z) (values : list (Z * Z)) (tail : Z)
    Require
      0 <= count && count <= capacity && Zlength(values) == count &&
      SegArray::full(ptr, count, values) *
      SegArray::undef_full(tail, capacity - count)
    Ensure emp
*/;

void qsort(Seg *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
/*@ qsort_seg
    With (contents : list (Z * Z))
    Require
      nmemb == Zlength(contents) &&
      SegmentAllocationSize(size, 1) &&
      SegmentsBounded(contents) &&
      SegArray::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Zlength(sorted) == nmemb &&
        Permutation(contents, sorted) &&
        SegmentsBounded(sorted) &&
        SegmentsSortedByLeft(sorted) &&
        SegArray::full(base, nmemb, sorted)
*/;

static int cmp(const void *A, const void *B)
{
    const Seg *a = A, *b = B;
    return a->l == b->l ? a->r - b->r : a->l - b->l;
}
static int overlap(Seg *a, int na, Seg *b, int nb)
/*@ With (left right : list (Z * Z))
    Require
      na == Zlength(left) && nb == Zlength(right) &&
      0 <= na && na <= 200000 && 0 <= nb && nb <= 200000 &&
      SegmentsBounded(left) && SegmentsBounded(right) &&
      SegArray::full(a, na, left) * SegArray::full(b, nb, right)
    Ensure
      exists right_after,
        Zlength(right_after) == nb &&
        Permutation(right, right_after) &&
        SegmentsBounded(right_after) &&
        DirectedOverlapMaximum(left, right, __return) &&
        0 <= __return && __return <= 1000000000 &&
        SegArray::full(a, na, left) * SegArray::full(b, nb, right_after)
*/
{
    if (!na || !nb)
        return 0;
    qsort(b, nb, sizeof *b, cmp)
        /*@ where (qsort_seg) contents = right */;
    int *pref = malloc(nb * sizeof *pref)
        /*@ where (malloc_int) capacity = nb */;
    /*@ Inv Assert
        exists sorted prefix,
          a == a@pre && na == na@pre && b == b@pre && nb == nb@pre &&
          na@pre == Zlength(left) && nb@pre == Zlength(right) &&
          0 < na@pre && na@pre <= 200000 &&
          0 < nb@pre && nb@pre <= 200000 &&
          0 <= i && i <= nb@pre && Zlength(prefix) == i &&
          Zlength(sorted) == nb@pre &&
          SegmentsBounded(left) &&
          Permutation(right, sorted) && SegmentsBounded(sorted) &&
          SegmentsSortedByLeft(sorted) &&
          PrefixRightMaxima(sorted, prefix, i) &&
          SegArray::full(a@pre, na@pre, left) *
          SegArray::full(b@pre, nb@pre, sorted) *
          IntArray::full(pref, i, prefix) *
          IntArray::undef_full(pref + i, nb@pre - i)
    */
    for (int i = 0; i < nb; i++)
        /*@ Assert
            exists sorted prefix,
              a == a@pre && na == na@pre && b == b@pre && nb == nb@pre &&
              na@pre == Zlength(left) && nb@pre == Zlength(right) &&
              0 < na@pre && na@pre <= 200000 &&
              0 < nb@pre && nb@pre <= 200000 &&
              0 <= i && i < nb@pre && Zlength(prefix) == i &&
              Zlength(sorted) == nb@pre &&
              SegmentsBounded(left) &&
              Permutation(right, sorted) && SegmentsBounded(sorted) &&
              SegmentsSortedByLeft(sorted) &&
              PrefixRightMaxima(sorted, prefix, i) &&
              SegArray::full(a@pre, na@pre, left) *
              SegArray::full(b@pre, i, sublist(0, i, sorted)) *
              data_at(&((b@pre + i)->l), int, fst(sorted[i])) *
              data_at(&((b@pre + i)->r), int, snd(sorted[i])) *
              SegArray::full(b@pre + i + 1, nb@pre - i - 1,
                             sublist(i + 1, nb@pre, sorted)) *
              IntArray::full(pref, i, prefix) *
              undef_data_at(pref + i, int) *
              IntArray::undef_full(pref + i + 1, nb@pre - i - 1)
        */
        pref[i] = i && pref[i - 1] > b[i].r ? pref[i - 1] : b[i].r;
    int best = 0;
    /*@ Inv Assert
        exists sorted prefix,
          a == a@pre && na == na@pre && b == b@pre && nb == nb@pre &&
          na@pre == Zlength(left) && nb@pre == Zlength(right) &&
          0 < na@pre && na@pre <= 200000 &&
          0 < nb@pre && nb@pre <= 200000 &&
          0 <= i && i <= na@pre &&
          0 <= best && best <= 1000000000 &&
          Zlength(sorted) == nb@pre && Zlength(prefix) == nb@pre &&
          SegmentsBounded(left) &&
          Permutation(right, sorted) && SegmentsBounded(sorted) &&
          SegmentsSortedByLeft(sorted) &&
          PrefixRightMaxima(sorted, prefix, nb@pre) &&
          DirectedOverlapMaximumPrefix(left, right, i, best) &&
          SegArray::full(a@pre, na@pre, left) *
          SegArray::full(b@pre, nb@pre, sorted) *
          IntArray::full(pref, nb@pre, prefix)
    */
    for (int i = 0; i < na; i++)
    {
        int lo = 0, hi = nb;
        /*@ Inv Assert
            exists sorted prefix,
              a == a@pre && na == na@pre && b == b@pre && nb == nb@pre &&
              na@pre == Zlength(left) && nb@pre == Zlength(right) &&
              0 < na@pre && na@pre <= 200000 &&
              0 < nb@pre && nb@pre <= 200000 &&
              0 <= i && i < na@pre &&
              0 <= lo && lo <= hi && hi <= nb@pre &&
              0 <= best && best <= 1000000000 &&
              Zlength(sorted) == nb@pre && Zlength(prefix) == nb@pre &&
              SegmentsBounded(left) &&
              Permutation(right, sorted) && SegmentsBounded(sorted) &&
              SegmentsSortedByLeft(sorted) &&
              PrefixRightMaxima(sorted, prefix, nb@pre) &&
              DirectedOverlapMaximumPrefix(left, right, i, best) &&
              UpperBoundBracket(sorted, fst(left[i]), lo, hi) &&
              SegArray::full(a@pre, na@pre, left) *
              SegArray::full(b@pre, nb@pre, sorted) *
              IntArray::full(pref, nb@pre, prefix)
        */
        while (lo < hi)
        {
            int md = (lo + hi) / 2;
            /*@ Assert
                exists sorted prefix,
                  a == a@pre && na == na@pre && b == b@pre && nb == nb@pre &&
                  na@pre == Zlength(left) && nb@pre == Zlength(right) &&
                  0 < na@pre && na@pre <= 200000 &&
                  0 < nb@pre && nb@pre <= 200000 &&
                  0 <= i && i < na@pre &&
                  0 <= lo && lo <= md && md < hi && hi <= nb@pre &&
                  0 <= best && best <= 1000000000 &&
                  Zlength(sorted) == nb@pre && Zlength(prefix) == nb@pre &&
                  SegmentsBounded(left) &&
                  Permutation(right, sorted) && SegmentsBounded(sorted) &&
                  SegmentsSortedByLeft(sorted) &&
                  PrefixRightMaxima(sorted, prefix, nb@pre) &&
                  DirectedOverlapMaximumPrefix(left, right, i, best) &&
                  UpperBoundBracket(sorted, fst(left[i]), lo, hi) &&
                  SegArray::full(a@pre, i, sublist(0, i, left)) *
                  data_at(&((a@pre + i)->l), int, fst(left[i])) *
                  data_at(&((a@pre + i)->r), int, snd(left[i])) *
                  SegArray::full(a@pre + i + 1, na@pre - i - 1,
                                 sublist(i + 1, na@pre, left)) *
                  SegArray::full(b@pre, md, sublist(0, md, sorted)) *
                  data_at(&((b@pre + md)->l), int, fst(sorted[md])) *
                  data_at(&((b@pre + md)->r), int, snd(sorted[md])) *
                  SegArray::full(b@pre + md + 1, nb@pre - md - 1,
                                 sublist(md + 1, nb@pre, sorted)) *
                  IntArray::full(pref, nb@pre, prefix)
            */
            if (b[md].l <= a[i].l)
                lo = md + 1;
            else
                hi = md;
        }
        /*@ Assert
            exists sorted prefix,
              a == a@pre && na == na@pre && b == b@pre && nb == nb@pre &&
              na@pre == Zlength(left) && nb@pre == Zlength(right) &&
              0 < na@pre && na@pre <= 200000 &&
              0 < nb@pre && nb@pre <= 200000 &&
              0 <= i && i < na@pre &&
              0 <= lo && lo == hi && hi <= nb@pre &&
              0 <= best && best <= 1000000000 &&
              Zlength(sorted) == nb@pre && Zlength(prefix) == nb@pre &&
              SegmentsBounded(left) &&
              Permutation(right, sorted) && SegmentsBounded(sorted) &&
              SegmentsSortedByLeft(sorted) &&
              PrefixRightMaxima(sorted, prefix, nb@pre) &&
              DirectedOverlapMaximumPrefix(left, right, i, best) &&
              UpperBoundBracket(sorted, fst(left[i]), lo, hi) &&
              SegArray::full(a@pre, i, sublist(0, i, left)) *
              data_at(&((a@pre + i)->l), int, fst(left[i])) *
              data_at(&((a@pre + i)->r), int, snd(left[i])) *
              SegArray::full(a@pre + i + 1, na@pre - i - 1,
                             sublist(i + 1, na@pre, left)) *
              SegArray::full(b@pre, nb@pre, sorted) *
              IntArray::full(pref, nb@pre, prefix)
        */
        if (lo)
        {
            int x = pref[lo - 1] < a[i].r ? pref[lo - 1] : a[i].r;
            x -= a[i].l;
            if (x > best)
                best = x;
        }
    }
    free(pref) /*@ where (free_int) capacity = nb */;
    return best;
}
/* QCP_INSERT_BEGIN:P087_1513F_swapping_problem.support */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P087_1513F_swapping_problem_lib */
/* QCP_INSERT_END:P087_1513F_swapping_problem.support */
/*@ Extern Coq
      (IncreasingIntervals : list Z -> list Z -> Z -> list (Z * Z))
      (DecreasingIntervals : list Z -> list Z -> Z -> list (Z * Z))
*/
static i64 solver(int n, const int *a,
                  const int *b) /* QCP_INSERT_BEGIN:P087_1513F_swapping_problem.contract */

/*@ With (values : list Z)
             (b_data : list Z)
    Require
      1 <= Zlength(values) && Zlength(values) <= 200000 &&
      Zlength(b_data) == Zlength(values) &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 1000000000)) &&
      (forall i, (0 <= i && i < Zlength(b_data)) => (1 <= b_data[i] && b_data[i] <= 1000000000)) &&
      n == Zlength(values) &&
      IntArray::full(a, n, values) * IntArray::full(b, n, b_data)
    Ensure
      Spec(values, b_data, __return) &&
      IntArray::full(a, n, values) * IntArray::full(b, n, b_data)
*/
/* QCP_INSERT_END:P087_1513F_swapping_problem.contract */
{
    Seg *x = malloc(n * sizeof *x) /*@ where (malloc_seg) capacity = n */,
        *y = malloc(n * sizeof *y) /*@ where (malloc_seg) capacity = n */;
    int nx = 0, ny = 0;
    i64 base = 0;
    /*@ Inv Assert
        exists increasing decreasing,
          n == n@pre && a == a@pre && b == b@pre &&
          n@pre == Zlength(values) &&
          Zlength(b_data) == Zlength(values) &&
          1 <= n@pre && n@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 1000000000)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= b_data[k] && b_data[k] <= 1000000000)) &&
          0 <= i && i <= n@pre &&
          0 <= nx && nx <= i && 0 <= ny && ny <= i &&
          Zlength(increasing) == nx && Zlength(decreasing) == ny &&
          0 <= base && base <= 999999999 * i &&
          SolverScanState(values, b_data, i, base, increasing, decreasing) &&
          SegmentsBounded(increasing) && SegmentsBounded(decreasing) &&
          IntArray::full(a@pre, n@pre, values) *
          IntArray::full(b@pre, n@pre, b_data) *
          SegArray::full(x, nx, increasing) *
          SegArray::undef_full(x + nx, n@pre - nx) *
          SegArray::full(y, ny, decreasing) *
          SegArray::undef_full(y + ny, n@pre - ny)
    */
    for (int i = 0; i < n; i++)
    {
        int d = a[i] - b[i];
        if (d < 0)
        {
            /*@ Assert
                exists increasing decreasing,
                  n == n@pre && a == a@pre && b == b@pre &&
                  n@pre == Zlength(values) &&
                  Zlength(b_data) == Zlength(values) &&
                  1 <= n@pre && n@pre <= 200000 &&
                  (forall k, (0 <= k && k < n@pre) =>
                    (1 <= values[k] && values[k] <= 1000000000)) &&
                  (forall k, (0 <= k && k < n@pre) =>
                    (1 <= b_data[k] && b_data[k] <= 1000000000)) &&
                  0 <= i && i < n@pre &&
                  0 <= nx && nx <= i && 0 <= ny && ny <= i &&
                  Zlength(increasing) == nx && Zlength(decreasing) == ny &&
                  0 <= base && base <= 999999999 * i &&
                  d == values[i] - b_data[i] && d < 0 &&
                  SolverScanState(values, b_data, i, base,
                                  increasing, decreasing) &&
                  SegmentsBounded(increasing) && SegmentsBounded(decreasing) &&
                  IntArray::full(a@pre, n@pre, values) *
                  IntArray::full(b@pre, n@pre, b_data) *
                  SegArray::full(x, nx, increasing) *
                  undef_data_at(&((x + nx)->l), int) *
                  undef_data_at(&((x + nx)->r), int) *
                  SegArray::undef_full(x + nx + 1, n@pre - nx - 1) *
                  SegArray::full(y, ny, decreasing) *
                  SegArray::undef_full(y + ny, n@pre - ny)
            */
            base -= d;
            x[nx].l = a[i];
            x[nx].r = b[i];
            nx++;
        }
        else if (d > 0)
        {
            /*@ Assert
                exists increasing decreasing,
                  n == n@pre && a == a@pre && b == b@pre &&
                  n@pre == Zlength(values) &&
                  Zlength(b_data) == Zlength(values) &&
                  1 <= n@pre && n@pre <= 200000 &&
                  (forall k, (0 <= k && k < n@pre) =>
                    (1 <= values[k] && values[k] <= 1000000000)) &&
                  (forall k, (0 <= k && k < n@pre) =>
                    (1 <= b_data[k] && b_data[k] <= 1000000000)) &&
                  0 <= i && i < n@pre &&
                  0 <= nx && nx <= i && 0 <= ny && ny <= i &&
                  Zlength(increasing) == nx && Zlength(decreasing) == ny &&
                  0 <= base && base <= 999999999 * i &&
                  d == values[i] - b_data[i] && d > 0 &&
                  SolverScanState(values, b_data, i, base,
                                  increasing, decreasing) &&
                  SegmentsBounded(increasing) && SegmentsBounded(decreasing) &&
                  IntArray::full(a@pre, n@pre, values) *
                  IntArray::full(b@pre, n@pre, b_data) *
                  SegArray::full(x, nx, increasing) *
                  SegArray::undef_full(x + nx, n@pre - nx) *
                  SegArray::full(y, ny, decreasing) *
                  undef_data_at(&((y + ny)->l), int) *
                  undef_data_at(&((y + ny)->r), int) *
                  SegArray::undef_full(y + ny + 1, n@pre - ny - 1)
            */
            base += d;
            y[ny].l = b[i];
            y[ny].r = a[i];
            ny++;
        }
    }
    /*@ Assert
          n == n@pre && a == a@pre && b == b@pre &&
          n@pre == Zlength(values) &&
          Zlength(b_data) == Zlength(values) &&
          1 <= n@pre && n@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 1000000000)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= b_data[k] && b_data[k] <= 1000000000)) &&
          nx == Zlength(IncreasingIntervals(values, b_data, n@pre)) &&
          ny == Zlength(DecreasingIntervals(values, b_data, n@pre)) &&
          0 <= nx && nx <= n@pre && 0 <= ny && ny <= n@pre &&
          0 <= base && base <= 999999999 * n@pre &&
          base == PairDistanceSum(values, b_data) &&
          SegmentsBounded(IncreasingIntervals(values, b_data, n@pre)) &&
          SegmentsBounded(DecreasingIntervals(values, b_data, n@pre)) &&
          IntArray::full(a@pre, n@pre, values) *
          IntArray::full(b@pre, n@pre, b_data) *
          SegArray::full(x, nx, IncreasingIntervals(values, b_data, n@pre)) *
          SegArray::undef_full(x + nx, n@pre - nx) *
          SegArray::full(y, ny, DecreasingIntervals(values, b_data, n@pre)) *
          SegArray::undef_full(y + ny, n@pre - ny)
    */
    int p = overlap(x, nx, y, ny)
        /*@ where left = IncreasingIntervals(values, b_data, n),
                   right = DecreasingIntervals(values, b_data, n) */,
        q = overlap(y, ny, x, nx),
        best = p > q ? p : q;
    /*@ Assert
        exists increasing_after decreasing_after,
          n == n@pre && a == a@pre && b == b@pre &&
          n@pre == Zlength(values) && Zlength(b_data) == Zlength(values) &&
          1 <= n@pre && n@pre <= 200000 &&
          base == PairDistanceSum(values, b_data) &&
          0 <= base && base <= 999999999 * n@pre &&
          0 <= best && best <= 1000000000 &&
          SwappingOverlapMaximum(values, b_data, best) &&
          Spec(values, b_data, base - 2 * best) &&
          Zlength(increasing_after) == nx && Zlength(decreasing_after) == ny &&
          data_at(&p, int, p) * data_at(&q, int, q) *
          IntArray::full(a@pre, n@pre, values) *
          IntArray::full(b@pre, n@pre, b_data) *
          SegArray::full(x, nx, increasing_after) *
          SegArray::undef_full(x + nx, n@pre - nx) *
          SegArray::full(y, ny, decreasing_after) *
          SegArray::undef_full(y + ny, n@pre - ny)
    */
    free(y) /*@ where (free_seg_mixed) capacity = n, count = ny,
                       tail = y + ny */;
    free(x) /*@ where (free_seg_mixed) capacity = n, count = nx,
                       tail = x + nx */;
    return base - 2LL * best;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     int *a = malloc(n * sizeof *a), *b = malloc(n * sizeof *b);
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     for (int i = 0; i < n; i++)
//         scanf("%d", &b[i]);
//     printf("%lld\n", solver(n, a, b));
//     free(b);
//     free(a);
//     return 0;
// }
