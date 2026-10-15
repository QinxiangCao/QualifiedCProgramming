// #include <stdio.h>
// #include <stdlib.h>
typedef long long i64;
typedef unsigned long size_t;
/*@ Extern Coq
      (GcdResult : Z -> Z -> Z -> Prop)
      (MinValue : Z -> Z -> Z -> Prop)
*/
static i64 gcdll(i64 a, i64 b)
/*@ gcdll_spec
    Require 0 <= a && a <= 1000000000 && 0 <= b && b <= 1000000000
    Ensure GcdResult(a@pre, b@pre, __return)
*/
{
    /*@ Inv Assert
          exists g,
            0 <= a && a <= 1000000000 &&
            0 <= b && b <= 1000000000 &&
            GcdResult(a, b, g) && GcdResult(a@pre, b@pre, g)
    */
    while (b)
    {
        i64 t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static int cmpi(const void *A, const void *B)
/*@ With (x y : Z)
    Require
      0 <= x && x <= 100000 && 0 <= y && y <= 100000 &&
      data_at(A, int, x) * data_at(B, int, y)
    Ensure
      __return == x - y &&
      data_at(A, int, x) * data_at(B, int, y)
*/
{
    return *(const int *)A - *(const int *)B;
}
/* QCP_INSERT_BEGIN:P089_1891E_brukhovich_and_exams.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P089_1891E_brukhovich_and_exams_lib */
/* QCP_INSERT_END:P089_1891E_brukhovich_and_exams.support */
/*@ Extern Coq
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (AllOnePrefix : list Z -> Z -> Z -> Prop)
      (CoprimeEdgePrefixCount : list Z -> Z -> Z -> Prop)
      (PairSavingsPrefix : list Z -> Z -> Z -> Prop)
      (PairSavingsScan : list Z -> Z -> Z -> Z -> Z -> Prop)
      (PairRunSuffix : list Z -> Z -> Z -> Prop)
      (InteriorOneRunPrefix : list Z -> Z -> list Z -> Prop)
      (OneRunScanState : list Z -> Z -> Z -> list Z -> Prop)
      (GreedyBlockState : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OptimizationSafetyBounds : Z -> Z -> list Z -> Prop)
      (JointPairBlockPrefix : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (ExamCompetitorChargingPrefix : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (ExamBlockCollectionCertificate : list Z -> Z -> Z -> list Z -> Prop)
      (ExamJointOptimizationCertificate : list Z -> Z -> Z -> list Z -> Prop)
      (ExamPrefixLowerBound : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (ExamGreedyAttainability : list Z -> Z -> Z -> list Z -> Prop)
      (CanonicalInteriorOneRunPrefix : list Z -> Z -> list Z -> Prop)
      (CanonicalOneRunScanState : list Z -> Z -> Z -> list Z -> Prop)
      (CanonicalExamBlockCollectionCertificate : list Z -> Z -> Z -> list Z -> Prop)
      (FinalBudgetResult : Z -> Z -> Z -> Prop)
      (ExamOptimizationSummary : list Z -> Z -> Z -> list Z -> Prop)
*/

void *malloc(unsigned long size)
/*@ malloc_int
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/;

void qsort(int *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
/*@ qsort_int_prefix
    With (contents : list Z)
    Require
      nmemb == Zlength(contents) && size == sizeof(int) &&
      IntArray::seg(base, 0, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) && increasing(sorted) &&
        Zlength(sorted) == nmemb &&
        IntArray::seg(base, 0, nmemb, sorted)
*/;

void free(void *ptr)
/*@ free_int_prefix
    With (cap used : Z) (contents : list Z)
    Require
      0 <= used && used <= cap &&
      IntArray::seg(ptr, 0, used, contents) *
      IntArray::undef_seg(ptr, used, cap)
    Ensure emp
*/;
static int solver(int n, int k,
                  const i64 *a) /* QCP_INSERT_BEGIN:P089_1891E_brukhovich_and_exams.contract */

/*@ With (values : list Z)
    Require
      1 <= k && k <= Zlength(values) &&
      Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (0 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) &&
      Int64Array::full(a, n, values)
    Ensure
      Spec(k, values, __return) &&
      Int64Array::full(a, n, values)
*/
/* QCP_INSERT_END:P089_1891E_brukhovich_and_exams.contract */
{
    int allone = 1;
    /*@ Inv Assert
          a == a@pre && n == n@pre && k == k@pre &&
          n@pre == Zlength(values) &&
          1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
          (forall j, (0 <= j && j < n@pre) =>
            (0 <= values[j] && values[j] <= 1000000000)) &&
          0 <= i && i <= n@pre && 0 <= allone && allone <= 1 &&
          AllOnePrefix(values, i, allone) &&
          Int64Array::full(a@pre, n@pre, values)
    */
    for (int i = 0; i < n; i++)
        if (a[i] != 1)
            allone = 0;
    if (allone)
        return k == n ? 0 : n - k;
    int sad = 0, two = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre && k == k@pre &&
          n@pre == Zlength(values) &&
          1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
          (forall j, (0 <= j && j < n@pre) =>
            (0 <= values[j] && values[j] <= 1000000000)) &&
          allone == 0 && two == 0 &&
          AllOnePrefix(values, n@pre, allone) &&
          0 <= i && i <= n@pre - 1 && 0 <= sad && sad <= i &&
          CoprimeEdgePrefixCount(values, i, sad) &&
          Int64Array::full(a@pre, n@pre, values)
    */
    for (int i = 0; i + 1 < n; i++)
        if (gcdll(a[i], a[i + 1]) == 1)
            sad++;
    /*@ Inv Assert
          a == a@pre && n == n@pre && k == k@pre &&
          n@pre == Zlength(values) &&
          1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
          (forall j, (0 <= j && j < n@pre) =>
            (0 <= values[j] && values[j] <= 1000000000)) &&
          allone == 0 &&
          AllOnePrefix(values, n@pre, allone) &&
          CoprimeEdgePrefixCount(values, n@pre - 1, sad) &&
          0 <= sad && sad < n@pre &&
          0 <= i && i <= n@pre && 0 <= two && 2 * two <= i &&
          (i == 0 || i == n@pre || values[i] == 1 || values[i - 1] == 1) &&
          PairSavingsPrefix(values, i, two) &&
          Int64Array::full(a@pre, n@pre, values)
    */
    for (int i = 0; i < n;)
    {
        if (a[i] == 1)
        {
            i++;
            continue;
        }
        int run = 0;
        /*@ Inv Assert
              a == a@pre && n == n@pre && k == k@pre &&
              n@pre == Zlength(values) &&
              1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
              (forall j, (0 <= j && j < n@pre) =>
                (0 <= values[j] && values[j] <= 1000000000)) &&
              allone == 0 &&
              AllOnePrefix(values, n@pre, allone) &&
              CoprimeEdgePrefixCount(values, n@pre - 1, sad) &&
              0 <= sad && sad < n@pre &&
              0 <= i && i < n@pre && 0 <= two && 0 <= run && run <= i + 1 &&
              PairRunSuffix(values, i + 1, run) &&
              exists scan_savings,
                scan_savings == two + run / 2 &&
                PairSavingsScan(values, i + 1, two, run, scan_savings) &&
                Int64Array::full(a@pre, n@pre, values)
        */
        while (i + 1 < n && a[i + 1] != 1)
        {
            if (gcdll(a[i], a[i + 1]) == 1)
                run++;
            else
            {
                two += run / 2;
                run = 0;
            }
            i++;
        }
        two += run / 2;
        i++;
    }
    /*@ Assert
          a == a@pre && n == n@pre && k == k@pre &&
          n@pre == Zlength(values) &&
          1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
          (forall j, (0 <= j && j < n@pre) =>
            (0 <= values[j] && values[j] <= 1000000000)) &&
          allone == 0 &&
          AllOnePrefix(values, n@pre, allone) &&
          CoprimeEdgePrefixCount(values, n@pre - 1, sad) &&
          PairSavingsPrefix(values, n@pre, two) &&
          CanonicalExamBlockCollectionCertificate(values, sad, two, nil) &&
          0 <= sad && sad < n@pre && 0 <= two && 2 * two <= n@pre &&
          Int64Array::full(a@pre, n@pre, values)
    */
    int *ones = malloc((size_t)n * sizeof *ones)
        /*@ where (malloc_int) cap = n */, oc = 0;
    /*@ Inv Assert
          exists blocks,
            a == a@pre && n == n@pre && k == k@pre &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= values[j] && values[j] <= 1000000000)) &&
            allone == 0 &&
            AllOnePrefix(values, n@pre, allone) &&
            ones != 0 && 0 <= i && i <= n@pre &&
            0 <= oc && oc <= i && Zlength(blocks) == oc &&
            (i == 0 || i == n@pre || values[i] != 1 || values[i - 1] != 1) &&
            CoprimeEdgePrefixCount(values, n@pre - 1, sad) &&
            PairSavingsPrefix(values, n@pre, two) &&
            CanonicalInteriorOneRunPrefix(values, i, blocks) &&
            JointPairBlockPrefix(values, i, sad, two, blocks) &&
            CanonicalExamBlockCollectionCertificate(values, sad, two, blocks) &&
            0 <= sad && sad < n@pre && 0 <= two && 2 * two <= n@pre &&
            Int64Array::full(a@pre, n@pre, values) *
            IntArray::seg(ones, 0, oc, blocks) *
            IntArray::undef_seg(ones, oc, n@pre)
    */
    for (int i = 0; i < n;)
    {
        if (a[i] != 1)
        {
            i++;
            continue;
        }
        int l = i;
        /*@ Inv Assert
              exists blocks,
                a == a@pre && n == n@pre && k == k@pre &&
                n@pre == Zlength(values) &&
                1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
                (forall j, (0 <= j && j < n@pre) =>
                  (0 <= values[j] && values[j] <= 1000000000)) &&
                allone == 0 &&
                AllOnePrefix(values, n@pre, allone) &&
                ones != 0 && 0 <= l && l <= i && i <= n@pre &&
                0 <= oc && oc <= l && Zlength(blocks) == oc &&
                (l == 0 || values[l - 1] != 1) &&
                values[l] == 1 &&
                CoprimeEdgePrefixCount(values, n@pre - 1, sad) &&
                PairSavingsPrefix(values, n@pre, two) &&
                CanonicalOneRunScanState(values, l, i, blocks) &&
                JointPairBlockPrefix(values, l, sad, two, blocks) &&
                CanonicalExamBlockCollectionCertificate(values, sad, two, blocks) &&
                0 <= sad && sad < n@pre && 0 <= two && 2 * two <= n@pre &&
                Int64Array::full(a@pre, n@pre, values) *
                IntArray::seg(ones, 0, oc, blocks) *
                IntArray::undef_seg(ones, oc, n@pre)
        */
        while (i < n && a[i] == 1)
            i++;
        if (l > 0 && i < n)
        {
            ones[oc] = i - l;
            oc++;
        }
    }
    /*@ Assert
          exists blocks,
            a == a@pre && n == n@pre && k == k@pre &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= values[j] && values[j] <= 1000000000)) &&
            allone == 0 &&
            AllOnePrefix(values, n@pre, allone) &&
            ones != 0 && 0 <= oc && oc <= n@pre && Zlength(blocks) == oc &&
            CoprimeEdgePrefixCount(values, n@pre - 1, sad) &&
            PairSavingsPrefix(values, n@pre, two) &&
            CanonicalInteriorOneRunPrefix(values, n@pre, blocks) &&
            JointPairBlockPrefix(values, n@pre, sad, two, blocks) &&
            CanonicalExamBlockCollectionCertificate(values, sad, two, blocks) &&
            ExamJointOptimizationCertificate(values, sad, two, blocks) &&
            ExamOptimizationSummary(values, sad, two, blocks) &&
            OptimizationSafetyBounds(sad, two, blocks) &&
            0 <= sad && sad < n@pre && 0 <= two && 2 * two <= n@pre &&
            Int64Array::full(a@pre, n@pre, values) *
            IntArray::seg(ones, 0, oc, blocks) *
            IntArray::undef_seg(ones, oc, n@pre)
    */
    /*@ Assert
          exists blocks,
            a == a@pre && n == n@pre && k == k@pre &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= values[j] && values[j] <= 1000000000)) &&
            allone == 0 &&
            AllOnePrefix(values, n@pre, allone) &&
            ones != 0 && 0 <= oc && oc <= n@pre && Zlength(blocks) == oc &&
            CoprimeEdgePrefixCount(values, n@pre - 1, sad) &&
            PairSavingsPrefix(values, n@pre, two) &&
            CanonicalInteriorOneRunPrefix(values, n@pre, blocks) &&
            JointPairBlockPrefix(values, n@pre, sad, two, blocks) &&
            CanonicalExamBlockCollectionCertificate(values, sad, two, blocks) &&
            ExamJointOptimizationCertificate(values, sad, two, blocks) &&
            ExamOptimizationSummary(values, sad, two, blocks) &&
            OptimizationSafetyBounds(sad, two, blocks) &&
            0 <= sad && sad < n@pre && 0 <= two && 2 * two <= n@pre &&
            Int64Array::full(a@pre, n@pre, values) *
            IntArray::seg(ones, 0, oc, blocks) *
            IntArray::undef_seg(ones, oc, n@pre)
    */
    int use = k < two ? k : two;
    sad -= 2 * use;
    k -= use;
    qsort(ones, oc, sizeof *ones, cmpi);
    /*@ Assert
          exists blocks sorted,
            a == a@pre && n == n@pre &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
            allone == 0 &&
            ones != 0 && 0 <= oc && oc <= n@pre &&
            Zlength(blocks) == oc && Zlength(sorted) == oc &&
            Permutation(blocks, sorted) && increasing(sorted) &&
            ExamOptimizationSummary(values, sad + 2 * use, two, blocks) &&
            OptimizationSafetyBounds(sad + 2 * use, two, blocks) &&
            MinValue(k@pre, two, use) && k == k@pre - use &&
            sad == (sad + 2 * use) - 2 * use &&
            0 <= use && use <= k@pre && 0 <= k && k <= n@pre &&
            Int64Array::full(a@pre, n@pre, values) *
            IntArray::seg(ones, 0, oc, sorted) *
            IntArray::undef_seg(ones, oc, n@pre)
    */
    /*@ Inv Assert
          exists blocks sorted base_sad,
            a == a@pre && n == n@pre &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
            allone == 0 &&
            ones != 0 && 0 <= oc && oc <= n@pre &&
            Zlength(blocks) == oc && Zlength(sorted) == oc &&
            Permutation(blocks, sorted) && increasing(sorted) &&
            ExamOptimizationSummary(values, base_sad, two, blocks) &&
            OptimizationSafetyBounds(base_sad, two, blocks) &&
            MinValue(k@pre, two, use) &&
            0 <= use && use <= k@pre &&
            0 <= i && i <= oc && 0 <= sad && sad <= n@pre &&
            0 <= k && k <= n@pre &&
            GreedyBlockState(sorted, i, k@pre - use,
              base_sad - 2 * use, k, sad) &&
            Int64Array::full(a@pre, n@pre, values) *
            IntArray::seg(ones, 0, oc, sorted) *
            IntArray::undef_seg(ones, oc, n@pre)
    */
    for (int i = 0; i < oc && ones[i] <= k; i++)
    {
        k -= ones[i];
        sad -= ones[i] + 1;
    }
    if (k > sad)
        k = sad;
    sad -= k;
    if (sad < 0)
        sad = 0;
    /*@ Assert
          exists blocks sorted base_sad,
            a == a@pre && n == n@pre &&
            n@pre == Zlength(values) &&
            1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
            ones != 0 && 0 <= oc && oc <= n@pre &&
            Zlength(blocks) == oc && Zlength(sorted) == oc &&
            Permutation(blocks, sorted) && increasing(sorted) &&
            ExamOptimizationSummary(values, base_sad, two, blocks) &&
            Spec(k@pre, values, sad) && 0 <= sad && sad < n@pre &&
            0 <= allone && allone <= 1 &&
            0 <= use && use <= n@pre && -n@pre <= k && k <= n@pre &&
            Int64Array::full(a@pre, n@pre, values) *
            IntArray::seg(ones, 0, oc, sorted) *
            IntArray::undef_seg(ones, oc, n@pre)
    */
    free(ones);
    return sad;
}
// int main(void)
// {
//     int T;
//     if (scanf("%d", &T) != 1)
//         return 0;
//     while (T--)
//     {
//         int n, k;
//         scanf("%d%d", &n, &k);
//         i64 *a = malloc((size_t)n * sizeof *a);
//         for (int i = 0; i < n; i++)
//             scanf("%lld", &a[i]);
//         printf("%d\n", solver(n, k, a));
//         free(a);
//     }
//     return 0;
// }
