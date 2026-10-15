/* Codeforces 276/C - Little Girl and Maximum Sum */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

static int cmp_ll(const void *x, const void *y)
{
    long long a = *(const long long *)x, b = *(const long long *)y;
    return (a > b) - (a < b);
}

/* QCP_INSERT_BEGIN:P043_276C_little_girl_and_maximum_sum.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : list Z -> list (Z*Z) -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P043_276C_little_girl_and_maximum_sum_lib */
/* QCP_INSERT_END:P043_276C_little_girl_and_maximum_sum.support */
/*@ Extern Coq
      (increasing : list Z -> Prop)
      (DifferencePrefix : list (Z*Z) -> Z -> Z -> list Z -> Prop)
      (CoveragePrefixState : list (Z*Z) -> Z -> Z -> list Z -> Prop)
      (CoverageProfile : list (Z*Z) -> Z -> list Z -> Prop)
      (DotProductPrefix : list Z -> list Z -> Z -> Z -> Prop)
*/

void *calloc(unsigned long nmemb, unsigned long size)
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

void qsort(long long *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
/*@ With (contents : list Z)
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

static long long solver(long long *a, int n, const int *left, const int *right, int q)/* QCP_INSERT_BEGIN:P043_276C_little_girl_and_maximum_sum.contract */

/*@ With (values : list Z)
             (queries : list (Z*Z))
             (lefts rights : list Z)
    Require
      1 <= Zlength(values) && Zlength(values) <= 200000 &&
      1 <= Zlength(queries) && Zlength(queries) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 200000)) &&
      (forall i, (0 <= i && i < Zlength(queries)) => ((0 <= fst(queries[i]) && fst(queries[i]) <= snd(queries[i])) && (snd(queries[i]) < Zlength(values)))) &&
      n == Zlength(values) &&
      q == Zlength(queries) &&
      Zlength(lefts) == q && Zlength(rights) == q &&
      (forall i, (0 <= i && i < q) =>
        (fst(queries[i]) == lefts[i] - 1 &&
         snd(queries[i]) == rights[i] - 1)) &&
      Int64Array::full(a, n, values) *
      IntArray::full(left, q, lefts) *
      IntArray::full(right, q, rights)
    Ensure
      exists values_after,
        Spec(values, queries, __return) &&
        Permutation(values, values_after) &&
        Int64Array::full(a, n, values_after) *
        IntArray::full(left, q, lefts) *
        IntArray::full(right, q, rights)
*/
/* QCP_INSERT_END:P043_276C_little_girl_and_maximum_sum.contract */

{
    long long *diff = calloc((size_t)n + 1, sizeof(*diff))
      /*@ where (calloc_int64) cap = n + 1 */;
    /*@ Inv Assert
        exists diff_data,
          a == a@pre && n == n@pre && left == left@pre &&
          right == right@pre && q == q@pre && diff != 0 &&
          n@pre == Zlength(values) && q@pre == Zlength(queries) &&
          Zlength(lefts) == q@pre && Zlength(rights) == q@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          1 <= q@pre && q@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 200000)) &&
          (forall k, (0 <= k && k < q@pre) =>
            ((0 <= fst(queries[k]) && fst(queries[k]) <= snd(queries[k])) &&
             snd(queries[k]) < n@pre)) &&
          (forall k, (0 <= k && k < q@pre) =>
            (fst(queries[k]) == lefts[k] - 1 &&
             snd(queries[k]) == rights[k] - 1)) &&
          0 <= i && i <= q@pre &&
          DifferencePrefix(queries, n@pre, i, diff_data) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
            (-i <= diff_data[k] && diff_data[k] <= i)) &&
          Int64Array::full(a@pre, n@pre, values) *
          IntArray::full(left@pre, q@pre, lefts) *
          IntArray::full(right@pre, q@pre, rights) *
          Int64Array::full(diff, n@pre + 1, diff_data)
    */
    for (int i = 0; i < q; ++i) {
        /*@ 0 <= lefts[i] - 1 && lefts[i] - 1 < n@pre &&
            0 <= rights[i] && rights[i] <= n@pre by local */
        ++diff[left[i] - 1];
        --diff[right[i]];
    }
    /*@ Inv Assert
        exists diff_data,
          a == a@pre && n == n@pre && left == left@pre &&
          right == right@pre && q == q@pre && diff != 0 &&
          n@pre == Zlength(values) && q@pre == Zlength(queries) &&
          Zlength(lefts) == q@pre && Zlength(rights) == q@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          1 <= q@pre && q@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 200000)) &&
          (forall k, (0 <= k && k < q@pre) =>
            ((0 <= fst(queries[k]) && fst(queries[k]) <= snd(queries[k])) &&
             snd(queries[k]) < n@pre)) &&
          (forall k, (0 <= k && k < q@pre) =>
            (fst(queries[k]) == lefts[k] - 1 &&
             snd(queries[k]) == rights[k] - 1)) &&
          1 <= i && i <= n@pre &&
          CoveragePrefixState(queries, n@pre, i, diff_data) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
            (-q@pre <= diff_data[k] && diff_data[k] <= q@pre)) &&
          Int64Array::full(a@pre, n@pre, values) *
          IntArray::full(left@pre, q@pre, lefts) *
          IntArray::full(right@pre, q@pre, rights) *
          Int64Array::full(diff, n@pre + 1, diff_data)
    */
    for (int i = 1; i < n; ++i)
        diff[i] += diff[i - 1];
    /*@ Assert
        exists frequencies tail,
          a == a@pre && n == n@pre && left == left@pre &&
          right == right@pre && q == q@pre && diff != 0 &&
          n@pre == Zlength(values) && q@pre == Zlength(queries) &&
          Zlength(lefts) == q@pre && Zlength(rights) == q@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          1 <= q@pre && q@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 200000)) &&
          (forall k, (0 <= k && k < q@pre) =>
            ((0 <= fst(queries[k]) && fst(queries[k]) <= snd(queries[k])) &&
             snd(queries[k]) < n@pre)) &&
          Zlength(frequencies) == n@pre && Zlength(tail) == 1 &&
          CoverageProfile(queries, n@pre, frequencies) &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 <= frequencies[k] && frequencies[k] <= q@pre)) &&
          Int64Array::full(a@pre, n@pre, values) *
          IntArray::full(left@pre, q@pre, lefts) *
          IntArray::full(right@pre, q@pre, rights) *
          Int64Array::full(diff, n@pre, frequencies) *
          Int64Array::full(diff + n@pre * sizeof(long long), 1, tail)
    */
    qsort(a, (size_t)n, sizeof(*a), cmp_ll);
    /*@ Assert
        exists values_sorted frequencies tail,
          a == a@pre && n == n@pre && left == left@pre &&
          right == right@pre && q == q@pre && diff != 0 &&
          n@pre == Zlength(values) && q@pre == Zlength(queries) &&
          Zlength(lefts) == q@pre && Zlength(rights) == q@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          1 <= q@pre && q@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 200000)) &&
          (forall k, (0 <= k && k < q@pre) =>
            ((0 <= fst(queries[k]) && fst(queries[k]) <= snd(queries[k])) &&
             snd(queries[k]) < n@pre)) &&
          Zlength(values_sorted) == n@pre &&
          Zlength(frequencies) == n@pre && Zlength(tail) == 1 &&
          Permutation(values, values_sorted) && increasing(values_sorted) &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values_sorted[k] && values_sorted[k] <= 200000)) &&
          CoverageProfile(queries, n@pre, frequencies) &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 <= frequencies[k] && frequencies[k] <= q@pre)) &&
          Int64Array::full(a@pre, n@pre, values_sorted) *
          IntArray::full(left@pre, q@pre, lefts) *
          IntArray::full(right@pre, q@pre, rights) *
          Int64Array::full(diff, n@pre, frequencies) *
          Int64Array::full(diff + n@pre * sizeof(long long), 1, tail)
    */
    qsort(diff, (size_t)n, sizeof(*diff), cmp_ll);
    /*@ Assert
        exists values_sorted frequencies frequencies_sorted tail,
          a == a@pre && n == n@pre && left == left@pre &&
          right == right@pre && q == q@pre && diff != 0 &&
          n@pre == Zlength(values) && q@pre == Zlength(queries) &&
          Zlength(lefts) == q@pre && Zlength(rights) == q@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          1 <= q@pre && q@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 200000)) &&
          (forall k, (0 <= k && k < q@pre) =>
            ((0 <= fst(queries[k]) && fst(queries[k]) <= snd(queries[k])) &&
             snd(queries[k]) < n@pre)) &&
          Zlength(values_sorted) == n@pre &&
          Zlength(frequencies) == n@pre &&
          Zlength(frequencies_sorted) == n@pre && Zlength(tail) == 1 &&
          Permutation(values, values_sorted) && increasing(values_sorted) &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values_sorted[k] && values_sorted[k] <= 200000)) &&
          CoverageProfile(queries, n@pre, frequencies) &&
          Permutation(frequencies, frequencies_sorted) &&
          increasing(frequencies_sorted) &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 <= frequencies_sorted[k] && frequencies_sorted[k] <= q@pre)) &&
          Int64Array::full(a@pre, n@pre, values_sorted) *
          IntArray::full(left@pre, q@pre, lefts) *
          IntArray::full(right@pre, q@pre, rights) *
          Int64Array::full(diff, n@pre + 1, app(frequencies_sorted, tail))
    */
    long long answer = 0;
    /*@ Inv Assert
        exists values_sorted frequencies frequencies_sorted tail,
          a == a@pre && n == n@pre && left == left@pre &&
          right == right@pre && q == q@pre && diff != 0 &&
          n@pre == Zlength(values) && q@pre == Zlength(queries) &&
          Zlength(lefts) == q@pre && Zlength(rights) == q@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          1 <= q@pre && q@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values[k] && values[k] <= 200000)) &&
          (forall k, (0 <= k && k < q@pre) =>
            ((0 <= fst(queries[k]) && fst(queries[k]) <= snd(queries[k])) &&
             snd(queries[k]) < n@pre)) &&
          0 <= i && i <= n@pre &&
          Zlength(values_sorted) == n@pre &&
          Zlength(frequencies) == n@pre &&
          Zlength(frequencies_sorted) == n@pre && Zlength(tail) == 1 &&
          Permutation(values, values_sorted) && increasing(values_sorted) &&
          CoverageProfile(queries, n@pre, frequencies) &&
          Permutation(frequencies, frequencies_sorted) &&
          increasing(frequencies_sorted) &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= values_sorted[k] && values_sorted[k] <= 200000)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 <= frequencies_sorted[k] && frequencies_sorted[k] <= q@pre)) &&
          0 <= answer && answer <= i * 200000 * q@pre &&
          DotProductPrefix(values_sorted, frequencies_sorted, i, answer) &&
          Int64Array::full(a@pre, n@pre, values_sorted) *
          IntArray::full(left@pre, q@pre, lefts) *
          IntArray::full(right@pre, q@pre, rights) *
          Int64Array::full(diff, n@pre + 1, app(frequencies_sorted, tail))
    */
    for (int i = 0; i < n; ++i)
        answer += a[i] * diff[i];
    free(diff) /*@ where (free_int64) */;
    return answer;
}

// int main(void)
// {
//     int n, q; if (scanf("%d %d", &n, &q) != 2) return 0;
//     long long *a = malloc((size_t)n * sizeof(*a));
//     int *left = malloc((size_t)q * sizeof(*left)), *right = malloc((size_t)q * sizeof(*right));
//     for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//     for (int i = 0; i < q; ++i) scanf("%d %d", &left[i], &right[i]);
//     printf("%lld\n", solver(a, n, left, right, q)); free(a); free(left); free(right);
//     return 0;
// }
