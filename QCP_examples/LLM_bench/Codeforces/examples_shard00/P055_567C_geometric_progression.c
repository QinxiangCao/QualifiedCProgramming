/* Codeforces 567/C - Geometric Progression */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/* QCP_INSERT_BEGIN:P055_567C_geometric_progression.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
      (CompareResult : Z -> Z -> Z -> Prop)
      (LowerBoundResult : list Z -> Z -> Z -> Prop)
      (KeyAt : list Z -> Z -> Z -> Prop)
      (UniqueKeys : list Z -> list Z -> Prop)
      (CompressionState : list Z -> Z -> Z -> list Z -> Prop)
      (RightBuildState : list Z -> Z -> list Z -> list Z -> Prop)
      (CountingState : Z -> list Z -> Z -> list Z -> list Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P055_567C_geometric_progression_lib */
/* QCP_INSERT_END:P055_567C_geometric_progression.support */

void *malloc(size_t size)
/*@ malloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      size == cap * sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::undef_full(__return, cap)
*/;

void *calloc(size_t nmemb, size_t size)
/*@ calloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, cap, repeat_Z(0, cap))
*/;

void qsort(long long *base, size_t nmemb, size_t size,
           int (*compar)(const void *, const void *))
/*@ qsort_int64
    With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      size == sizeof(long long) &&
      Int64Array::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        increasing(sorted) &&
        Zlength(sorted) == nmemb &&
        Int64Array::full(base, nmemb, sorted)
*/;

void free(void *ptr)
/*@ free_int64
    Require exists values cap,
      Int64Array::full(ptr, cap, values)
    Ensure emp
*/;

static int cmp_ll(const void *x, const void *y)
/*@ With (vx vy : Z)
    Require
      data_at(x, long long, vx) *
      data_at(y, long long, vy)
    Ensure
      CompareResult(vx, vy, __return) &&
      data_at(x, long long, vx) *
      data_at(y, long long, vy)
*/
{
    long long a = *(const long long *)x;
    long long b = *(const long long *)y;
    return (a > b) - (a < b);
}

static int lower_bound_ll(const long long *a, int n, long long x)
/*@ With (values : list Z)
    Require
      n == Zlength(values) &&
      0 <= n && n <= 200000 &&
      increasing(values) &&
      Int64Array::seg(a, 0, n, values)
    Ensure
      0 <= __return && __return <= n &&
      LowerBoundResult(values, x, __return) &&
      Int64Array::seg(a, 0, n, values)
*/
{
    int l = 0;
    int r = n;
    /*@ Inv Assert
          a == a@pre && n == n@pre && x == x@pre &&
          n@pre == Zlength(values) &&
          0 <= n@pre && n@pre <= 200000 &&
          0 <= l && l <= r && r <= n@pre &&
          increasing(values) &&
          (forall i, (0 <= i && i < l) => values[i] < x@pre) &&
          (forall i, (r <= i && i < n@pre) => x@pre <= values[i]) &&
          Int64Array::seg(a@pre, 0, n@pre, values)
    */
    while (l < r) {
        int m = (l + r) / 2;
        /*@ 0 <= m && m < n@pre by local */
        if (a[m] < x) {
            l = m + 1;
        } else {
            r = m;
        }
    }
    return l;
}

static long long solver(const long long *input, int n, long long k)/* QCP_INSERT_BEGIN:P055_567C_geometric_progression.contract */

/*@ With (values : list Z)
    Require
      1 <= k && k <= 200000 &&
      1 <= Zlength(values) && Zlength(values) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(values)) =>
        (-1000000000 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) &&
      Int64Array::full(input, n, values)
    Ensure
      Spec(k, values, __return) &&
      Int64Array::full(input, n, values)
*/
/* QCP_INSERT_END:P055_567C_geometric_progression.contract */

{
    long long *a = malloc((size_t)n * sizeof(*a))
      /*@ where (malloc_int64) cap = n */;
    long long *vals = malloc((size_t)n * sizeof(*vals))
      /*@ where (malloc_int64) cap = n */;

    /*@ Inv Assert
          input == input@pre && n == n@pre && k == k@pre &&
          a != 0 && vals != 0 &&
          n@pre == Zlength(values) &&
          1 <= k@pre && k@pre <= 200000 &&
          1 <= n@pre && n@pre <= 200000 &&
          (forall j, (0 <= j && j < n@pre) =>
            (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
          0 <= i && i <= n@pre &&
          Int64Array::full(input@pre, n@pre, values) *
          Int64Array::seg(a, 0, i, sublist(0, i, values)) *
          Int64Array::undef_seg(a, i, n@pre) *
          Int64Array::seg(vals, 0, i, sublist(0, i, values)) *
          Int64Array::undef_seg(vals, i, n@pre)
    */
    for (int i = 0; i < n; ++i) {
        a[i] = input[i];
        vals[i] = input[i];
    }

    /*@ Assert
          input == input@pre && n == n@pre && k == k@pre &&
          a != 0 && vals != 0 &&
          n@pre == Zlength(values) &&
          1 <= k@pre && k@pre <= 200000 &&
          1 <= n@pre && n@pre <= 200000 &&
          (forall j, (0 <= j && j < n@pre) =>
            (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
          Int64Array::full(input@pre, n@pre, values) *
          Int64Array::full(a, n@pre, values) *
          Int64Array::full(vals, n@pre, values)
    */
    qsort(vals, (size_t)n, sizeof(*vals), cmp_ll)
      /*@ where (qsort_int64) contents = values */;

    int un = 0;
    /*@ Inv Assert
          exists sorted storage,
            input == input@pre && n == n@pre && k == k@pre &&
            a != 0 && vals != 0 &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= 200000 &&
            1 <= n@pre && n@pre <= 200000 &&
            (forall j, (0 <= j && j < n@pre) =>
              (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
            Zlength(sorted) == n@pre && Zlength(storage) == n@pre &&
            Permutation(values, sorted) && increasing(sorted) &&
            0 <= i && i <= n@pre && 0 <= un && un <= i &&
            CompressionState(sorted, i, un, storage) &&
            Int64Array::full(input@pre, n@pre, values) *
            Int64Array::full(a, n@pre, values) *
            Int64Array::full(vals, n@pre, storage)
    */
    for (int i = 0; i < n; ++i) {
        if (i == 0 || vals[i] != vals[i - 1]) {
            vals[un] = vals[i];
            ++un;
        }
    }

    /*@ Assert
          exists sorted keys tail,
            input == input@pre && n == n@pre && k == k@pre &&
            a != 0 && vals != 0 &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= 200000 &&
            1 <= n@pre && n@pre <= 200000 &&
            1 <= un && un <= n@pre &&
            Zlength(sorted) == n@pre &&
            Zlength(keys) == un && Zlength(tail) == n@pre - un &&
            Permutation(values, sorted) && increasing(sorted) &&
            UniqueKeys(sorted, keys) &&
            (forall j, (0 <= j && j < n@pre) =>
              (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
            (forall j, (0 <= j && j < un) =>
              (-1000000000 <= keys[j] && keys[j] <= 1000000000)) &&
            Int64Array::full(input@pre, n@pre, values) *
            Int64Array::full(a, n@pre, values) *
            Int64Array::seg(vals, 0, un, keys) *
            Int64Array::seg(vals, un, n@pre, tail)
    */
    long long *left = calloc((size_t)un, sizeof(*left))
      /*@ where (calloc_int64) cap = un */;
    long long *right = calloc((size_t)un, sizeof(*right))
      /*@ where (calloc_int64) cap = un */;

    /*@ Inv Assert
          exists sorted keys tail left_data right_data,
            input == input@pre && n == n@pre && k == k@pre &&
            a != 0 && vals != 0 && left != 0 && right != 0 &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= 200000 &&
            1 <= n@pre && n@pre <= 200000 &&
            1 <= un && un <= n@pre &&
            Zlength(sorted) == n@pre &&
            Zlength(keys) == un && Zlength(tail) == n@pre - un &&
            Zlength(left_data) == un && Zlength(right_data) == un &&
            Permutation(values, sorted) && increasing(sorted) &&
            UniqueKeys(sorted, keys) &&
            (forall j, (0 <= j && j < n@pre) =>
              (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
            (forall j, (0 <= j && j < un) =>
              (-1000000000 <= keys[j] && keys[j] <= 1000000000)) &&
            0 <= i && i <= n@pre &&
            RightBuildState(values, i, keys, right_data) &&
            left_data == repeat_Z(0, un) &&
            (forall j, (0 <= j && j < un) =>
              (0 <= right_data[j] && right_data[j] <= i)) &&
            Int64Array::full(input@pre, n@pre, values) *
            Int64Array::full(a, n@pre, values) *
            Int64Array::seg(vals, 0, un, keys) *
            Int64Array::seg(vals, un, n@pre, tail) *
            Int64Array::full(left, un, left_data) *
            Int64Array::full(right, un, right_data)
    */
    for (int i = 0; i < n; ++i) {
        int index = lower_bound_ll(vals, un, a[i]);
        /*@ Assert
              exists sorted keys tail left_data right_data,
              input == input@pre && n == n@pre && k == k@pre &&
              a != 0 && vals != 0 && left != 0 && right != 0 &&
              n@pre == Zlength(values) &&
              1 <= k@pre && k@pre <= 200000 &&
              1 <= n@pre && n@pre <= 200000 &&
              1 <= un && un <= n@pre &&
              0 <= i && i < n@pre &&
              Zlength(sorted) == n@pre &&
              Zlength(keys) == un && Zlength(tail) == n@pre - un &&
              Zlength(left_data) == un && Zlength(right_data) == un &&
              Permutation(values, sorted) && increasing(sorted) &&
              UniqueKeys(sorted, keys) &&
              (forall j, (0 <= j && j < n@pre) =>
                (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
              (forall j, (0 <= j && j < un) =>
                (-1000000000 <= keys[j] && keys[j] <= 1000000000)) &&
              0 <= index && index < un &&
              KeyAt(keys, values[i], index) &&
              RightBuildState(values, i, keys, right_data) &&
              left_data == repeat_Z(0, un) &&
              (forall j, (0 <= j && j < un) =>
                (0 <= right_data[j] && right_data[j] <= i)) &&
              Int64Array::full(input@pre, n@pre, values) *
              Int64Array::full(a, n@pre, values) *
              Int64Array::seg(vals, 0, un, keys) *
              Int64Array::seg(vals, un, n@pre, tail) *
              Int64Array::full(left, un, left_data) *
              Int64Array::full(right, un, right_data)
        */
        ++right[index];
    }

    long long ans = 0;
    /*@ Inv Assert
          exists sorted keys tail left_data right_data,
            input == input@pre && n == n@pre && k == k@pre &&
            a != 0 && vals != 0 && left != 0 && right != 0 &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= 200000 &&
            1 <= n@pre && n@pre <= 200000 &&
            1 <= un && un <= n@pre &&
            Zlength(sorted) == n@pre &&
            Zlength(keys) == un && Zlength(tail) == n@pre - un &&
            Zlength(left_data) == un && Zlength(right_data) == un &&
            Permutation(values, sorted) && increasing(sorted) &&
            UniqueKeys(sorted, keys) &&
            (forall j, (0 <= j && j < n@pre) =>
              (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
            (forall j, (0 <= j && j < un) =>
              (-1000000000 <= keys[j] && keys[j] <= 1000000000)) &&
            0 <= i && i <= n@pre &&
            0 <= ans && ans <= n@pre * n@pre * n@pre &&
            CountingState(k@pre, values, i, keys, left_data, right_data, ans) &&
            (forall j, (0 <= j && j < un) =>
              (0 <= left_data[j] && left_data[j] <= i)) &&
            (forall j, (0 <= j && j < un) =>
              (0 <= right_data[j] && right_data[j] <= n@pre - i)) &&
            Int64Array::full(input@pre, n@pre, values) *
            Int64Array::full(a, n@pre, values) *
            Int64Array::seg(vals, 0, un, keys) *
            Int64Array::seg(vals, un, n@pre, tail) *
            Int64Array::full(left, un, left_data) *
            Int64Array::full(right, un, right_data)
    */
    for (int i = 0; i < n; ++i) {
        int ix = lower_bound_ll(vals, un, a[i]);
        /*@ Assert
              exists sorted keys tail left_data right_data,
              input == input@pre && n == n@pre && k == k@pre &&
              a != 0 && vals != 0 && left != 0 && right != 0 &&
              n@pre == Zlength(values) &&
              1 <= k@pre && k@pre <= 200000 &&
              1 <= n@pre && n@pre <= 200000 &&
              1 <= un && un <= n@pre &&
              0 <= i && i < n@pre &&
              0 <= ans && ans <= n@pre * n@pre * n@pre &&
              Zlength(sorted) == n@pre &&
              Zlength(keys) == un && Zlength(tail) == n@pre - un &&
              Zlength(left_data) == un && Zlength(right_data) == un &&
              Permutation(values, sorted) && increasing(sorted) &&
              UniqueKeys(sorted, keys) &&
              (forall j, (0 <= j && j < n@pre) =>
                (-1000000000 <= values[j] && values[j] <= 1000000000)) &&
              (forall j, (0 <= j && j < un) =>
                (-1000000000 <= keys[j] && keys[j] <= 1000000000)) &&
              0 <= ix && ix < un &&
              KeyAt(keys, values[i], ix) &&
              CountingState(k@pre, values, i, keys, left_data, right_data, ans) &&
              1 <= right_data[ix] && right_data[ix] <= n@pre - i &&
              (forall j, (0 <= j && j < un) =>
                (0 <= left_data[j] && left_data[j] <= i)) &&
              (forall j, (0 <= j && j < un) =>
                (0 <= right_data[j] && right_data[j] <= n@pre - i)) &&
              Int64Array::full(input@pre, n@pre, values) *
              Int64Array::full(a, n@pre, values) *
              Int64Array::seg(vals, 0, un, keys) *
              Int64Array::seg(vals, un, n@pre, tail) *
              Int64Array::full(left, un, left_data) *
              Int64Array::full(right, un, right_data)
        */
        --right[ix];
        if (a[i] % k == 0) {
            long long lo = a[i] / k;
            long long hi = a[i] * k;
            int li = lower_bound_ll(vals, un, lo);
            int ri = lower_bound_ll(vals, un, hi);
            if (li < un && vals[li] == lo &&
                ri < un && vals[ri] == hi) {
                ans += left[li] * right[ri];
            }
        }
        ++left[ix];
    }

    /*@ Assert
          exists keys tail left_data right_data,
            input == input@pre && n == n@pre && k == k@pre &&
            n@pre == Zlength(values) &&
            Spec(k@pre, values, ans) &&
            Zlength(keys) == un && Zlength(tail) == n@pre - un &&
            Zlength(left_data) == un && Zlength(right_data) == un &&
            Int64Array::full(input@pre, n@pre, values) *
            Int64Array::full(a, n@pre, values) *
            Int64Array::full(vals, n@pre, app(keys, tail)) *
            Int64Array::full(left, un, left_data) *
            Int64Array::full(right, un, right_data)
    */
    free(a) /*@ where (free_int64) */;
    free(vals) /*@ where (free_int64) */;
    free(left) /*@ where (free_int64) */;
    free(right) /*@ where (free_int64) */;
    return ans;
}

// int main(void)
// {
//     int n;
//     long long k;
//     if (scanf("%d %lld", &n, &k) != 2) return 0;
//     long long *a = malloc((size_t)n * sizeof(*a));
//     for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//     printf("%lld\n", solver(a, n, k));
//     free(a);
//     return 0;
// }
