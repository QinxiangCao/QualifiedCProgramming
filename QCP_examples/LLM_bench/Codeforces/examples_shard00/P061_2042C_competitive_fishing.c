/* Codeforces 2042/C - Competitive Fishing */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;
static int cmp_desc(const void *x, const void *y)
/*@ With (a b : Z)
    Require
      data_at(x, int, a) * data_at(y, int, b)
    Ensure
      ((b > a && __return == 1) ||
       (b < a && __return == -1) ||
       (b == a && __return == 0)) &&
      data_at(x, int, a) * data_at(y, int, b)
*/
{
    int a = *(const int *)x, b = *(const int *)y;
    return (b > a) - (b < a);
}
/* QCP_INSERT_BEGIN:P061_2042C_competitive_fishing.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Permutation : list Z -> list Z -> Prop)
      (decreasing : list Z -> Prop)
      (GainBuildState : list Z -> Z -> list Z -> Z -> Prop)
      (PreparedGains : list Z -> list Z -> Prop)
      (GainSearchState : Z -> list Z -> Z -> Z -> Prop)
      (FishingSearchResult : Z -> list Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P061_2042C_competitive_fishing_lib */
/* QCP_INSERT_END:P061_2042C_competitive_fishing.support */

void *malloc(unsigned long size)
/*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap && size == cap * sizeof(int)
    Ensure
      __return != 0 && IntArray::undef_full(__return, cap)
*/;

void qsort(int *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
/*@ With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      size == sizeof(int) &&
      IntArray::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        decreasing(sorted) &&
        Zlength(sorted) == nmemb &&
        IntArray::full(base, nmemb, sorted)
*/;

void free(void *ptr)
/*@ free_int
    With (values : list Z)
    Require
      IntArray::full(ptr, Zlength(values), values)
    Ensure emp
*/;

static int solver(const char *s, int n,
                  long long k) /* QCP_INSERT_BEGIN:P061_2042C_competitive_fishing.contract */

/*@ With (f : list Z)
    Require
      2 <= Zlength(f) && Zlength(f) <= 200000 &&
      1 <= k && k <= 1000000000 &&
      (forall i, (0 <= i && i < Zlength(f)) =>
        (f[i] == 48 || f[i] == 49)) &&
      n == Zlength(f) &&
      CharArray::full(s, n + 1, app(f, cons(0, nil)))
    Ensure
      Spec(k, f, __return) &&
      CharArray::full(s, n + 1, app(f, cons(0, nil)))
*/
/* QCP_INSERT_END:P061_2042C_competitive_fishing.contract */
{
    int *gain = malloc((size_t)(n - 1) * sizeof(*gain))
        /*@ where (malloc_int) cap = n - 1 */,
        sum = s[n - 1] == '1' ? 1 : -1;
    /*@ Inv Assert
        exists built_gains,
          s == s@pre && n == n@pre && k == k@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Zlength(f) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (f[j] == 48 || f[j] == 49)) &&
          -1 <= i && i <= n@pre - 2 &&
          -n@pre <= sum && sum <= n@pre &&
          Zlength(built_gains) == n@pre - i - 2 &&
          GainBuildState(f, i + 1, built_gains, sum) &&
          CharArray::full(s@pre, n@pre + 1, app(f, cons(0, nil))) *
          IntArray::undef_seg(gain, 0, i + 1) *
          IntArray::seg(gain, i + 1, n@pre - 1, built_gains)
    */
    for (int i = n - 2; i >= 0; --i)
    {
        gain[i] = sum;
        sum += s[i] == '1' ? 1 : -1;
    }
    /*@ Assert
        exists canonical_gains,
          s == s@pre && n == n@pre && k == k@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Zlength(f) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (f[j] == 48 || f[j] == 49)) &&
          Zlength(canonical_gains) == n@pre - 1 &&
          (forall j, (0 <= j && j < n@pre - 1) =>
            (-n@pre <= canonical_gains[j] && canonical_gains[j] <= n@pre)) &&
          -n@pre <= sum && sum <= n@pre &&
          GainBuildState(f, 0, canonical_gains, sum) &&
          CharArray::full(s@pre, n@pre + 1, app(f, cons(0, nil))) *
          IntArray::full(gain, n@pre - 1, canonical_gains)
    */
    qsort(gain, (size_t)(n - 1), sizeof(*gain), cmp_desc);
    /*@ Assert
        exists sorted_gains,
          s == s@pre && n == n@pre && k == k@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Zlength(f) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (f[j] == 48 || f[j] == 49)) &&
          Zlength(sorted_gains) == n@pre - 1 &&
          (forall j, (0 <= j && j < n@pre - 1) =>
            (-n@pre <= sorted_gains[j] && sorted_gains[j] <= n@pre)) &&
          -n@pre <= sum && sum <= n@pre &&
          PreparedGains(f, sorted_gains) &&
          CharArray::full(s@pre, n@pre + 1, app(f, cons(0, nil))) *
          IntArray::full(gain, n@pre - 1, sorted_gains)
    */
    long long cur = 0;
    int ans = -1;
    /*@ Inv Assert
        exists sorted_gains,
          s == s@pre && n == n@pre && k == k@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Zlength(f) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (f[j] == 48 || f[j] == 49)) &&
          0 <= i && i <= n@pre - 1 && ans == -1 &&
          -n@pre <= sum && sum <= n@pre &&
          -40000000000 <= cur && cur <= 40000000000 &&
          Zlength(sorted_gains) == n@pre - 1 &&
          (forall j, (0 <= j && j < n@pre - 1) =>
            (-n@pre <= sorted_gains[j] && sorted_gains[j] <= n@pre)) &&
          PreparedGains(f, sorted_gains) &&
          GainSearchState(k@pre, sorted_gains, i, cur) &&
          CharArray::full(s@pre, n@pre + 1, app(f, cons(0, nil))) *
          IntArray::full(gain, n@pre - 1, sorted_gains)
    */
    for (int i = 0; i < n - 1; ++i)
    {
        cur += gain[i];
        if (cur >= k)
        {
            ans = i + 2;
            break;
        }
    }
    /*@ Assert
        exists sorted_gains,
          s == s@pre && n == n@pre && k == k@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Zlength(f) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (f[j] == 48 || f[j] == 49)) &&
          -1 <= ans && ans <= n@pre &&
          -n@pre <= sum && sum <= n@pre &&
          -40000000000 <= cur && cur <= 40000000000 &&
          Zlength(sorted_gains) == n@pre - 1 &&
          PreparedGains(f, sorted_gains) &&
          FishingSearchResult(k@pre, f, sorted_gains, ans) &&
          Spec(k@pre, f, ans) &&
          CharArray::full(s@pre, n@pre + 1, app(f, cons(0, nil))) *
          IntArray::full(gain, Zlength(sorted_gains), sorted_gains)
    */
    /*@ Given sorted_gains */
    free(gain) /*@ where (free_int) values = sorted_gains */;
    return ans;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n;
//         long long k;
//         char *s;
//         scanf("%d %lld", &n, &k);
//         s = malloc((size_t)n + 1);
//         scanf("%s", s);
//         printf("%d\n", solver(s, n, k));
//         free(s);
//     }
//     return 0;
// }
