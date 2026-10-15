/* Codeforces 1977/C - Nikita and LCM */
// #include <stdio.h>
// #include <stdlib.h>
/*@ Extern Coq
      (GcdValue : Z -> Z -> Z)
      (LcmCapValue : Z -> Z -> Z -> Z -> Prop)
      (CompareResult : Z -> Z -> Z -> Prop)
*/
static long long gcdll(long long a, long long b)
/*@ Require
      1 <= a && a <= 1000000001 &&
      1 <= b && b <= 1000000000 && emp
    Ensure
      __return == GcdValue(a@pre, b@pre) && emp
*/
{
    /*@ Inv Assert
          1 <= a && a <= 1000000001 &&
          0 <= b && b <= 1000000000 &&
          GcdValue(a, b) == GcdValue(a@pre, b@pre) && emp
    */
    while (b)
    {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static long long lcm_cap(long long a, long long b, long long cap)
/*@ Require
      1 <= cap && cap <= 1000000000 &&
      1 <= a && a <= cap + 1 &&
      1 <= b && b <= cap && emp
    Ensure
      1 <= __return && __return <= cap@pre + 1 &&
      LcmCapValue(a@pre, b@pre, cap@pre, __return) && emp
*/
{
    long long g = gcdll(a, b);
    /*@ Assert
          a == a@pre && b == b@pre && cap == cap@pre &&
          1 <= cap@pre && cap@pre <= 1000000000 &&
          1 <= a@pre && a@pre <= cap@pre + 1 &&
          1 <= b@pre && b@pre <= cap@pre &&
          g == GcdValue(a@pre, b@pre) &&
          1 <= g && g <= b@pre && emp
    */
    if (a / g > cap / b)
        return cap + 1;
    long long x = a / g * b;
    return x > cap ? cap + 1 : x;
}
static int cmp_int(const void *x, const void *y)
/*@ With (vx vy : Z)
    Require
      data_at(x, int, vx) * data_at(y, int, vy)
    Ensure
      CompareResult(vx, vy, __return) &&
      data_at(x, int, vx) * data_at(y, int, vy)
*/
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}
/* QCP_INSERT_BEGIN:P063_1977C_nikita_and_lcm.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P063_1977C_nikita_and_lcm_lib */
/*@ Extern Coq
      (IntArray::undef_full : Z -> Z -> Assertion)
*/
/* QCP_INSERT_END:P063_1977C_nikita_and_lcm.support */

/*@ Extern Coq
      (GcdValue : Z -> Z -> Z)
      (LcmCapValue : Z -> Z -> Z -> Z -> Prop)
      (CompareResult : Z -> Z -> Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (CopyMaxState : list Z -> list Z -> Z -> Z -> Prop)
      (LcmPrefixState : list Z -> Z -> Z -> Z -> Prop)
      (DivisorBestState : list Z -> Z -> Z -> Z -> Z -> Prop)
      (DivisorScanState : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

void *malloc(unsigned long size)
/*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      size == cap * sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::undef_full(__return, cap)
*/;

void free(void *ptr)
/*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
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
        Zlength(sorted) == nmemb &&
        IntArray::full(base, nmemb, sorted)
*/;

static int solver(int *input, int n) /* QCP_INSERT_BEGIN:P063_1977C_nikita_and_lcm.contract */

/*@ With (a : list Z)
    Require
      1 <= Zlength(a) && Zlength(a) <= 2000 &&
      (forall i, (0 <= i && i < Zlength(a)) => (1 <= a[i] && a[i] <= 1000000000)) &&
      n == Zlength(a) && IntArray::full(input, n, a)
    Ensure
      Spec(a, __return) && IntArray::full(input, n, a)
*/
/* QCP_INSERT_END:P063_1977C_nikita_and_lcm.contract */
{
    /*@ Assert
          exists original,
            original == a &&
            input == input@pre && n == n@pre &&
            n@pre == Zlength(original) &&
            1 <= n@pre && n@pre <= 2000 &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= original[k] && original[k] <= 1000000000)) &&
            IntArray::full(input@pre, n@pre, original)
    */
    int *a = malloc(n * sizeof(*a))
        /*@ where (malloc_int) cap = n */;
    /*@ Given original */
    int mx = 0;
    long long all = 1;
    /*@ Inv
          exists copied,
            input == input@pre && n == n@pre && a != 0 &&
            n@pre == Zlength(original) &&
            1 <= n@pre && n@pre <= 2000 &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= original[k] && original[k] <= 1000000000)) &&
            0 <= i && i <= n@pre &&
            0 <= mx && mx <= 1000000000 &&
            CopyMaxState(original, copied, i, mx) &&
            IntArray::full(input@pre, n@pre, original) *
            IntArray::seg(a, 0, i, copied) *
            IntArray::undef_seg(a, i, n@pre)
    */
    for (int i = 0; i < n; ++i)
    {
        a[i] = input[i];
        if (a[i] > mx)
            mx = a[i];
    }
    /*@ Given copied
              finished_i from i */
    /*@
          finished_i == n@pre && Zlength(copied) == finished_i &&
          IntArray::seg(a, 0, finished_i, copied)
          which implies
          IntArray::full(a, n@pre, copied)
    */
    /*@ Inv
          input == input@pre && n == n@pre && a != 0 &&
            n@pre == Zlength(original) && Zlength(copied) == n@pre &&
            1 <= n@pre && n@pre <= 2000 &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= original[k] && original[k] <= 1000000000)) &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= copied[k] && copied[k] <= 1000000000)) &&
            1 <= mx && mx <= 1000000000 &&
            0 <= i && i <= n@pre &&
            1 <= all && all <= mx + 1 &&
            CopyMaxState(original, copied, n@pre, mx) &&
            LcmPrefixState(copied, i, mx, all) &&
            IntArray::full(input@pre, n@pre, original) *
            IntArray::full(a, n@pre, copied)
    */
    for (int i = 0; i < n; ++i)
        all = lcm_cap(all, a[i], mx);
    if (all != mx)
    {
        /*@
              input == input@pre && n == n@pre && a != 0 &&
                n@pre == Zlength(original) && Zlength(copied) == n@pre &&
                1 <= n@pre && n@pre <= 2000 &&
                1 <= mx && mx <= 1000000000 && all != mx &&
                CopyMaxState(original, copied, n@pre, mx) &&
                LcmPrefixState(copied, n@pre, mx, all) &&
                Spec(original, n@pre) &&
                IntArray::full(input@pre, n@pre, original) *
                IntArray::full(a, n@pre, copied)
        */
        free(a);
        return n;
    }
    qsort(a, n, sizeof(*a), cmp_int);
    /*@ Given sorted */
    /*@
          input == input@pre && n == n@pre && a != 0 &&
            n@pre == Zlength(original) && Zlength(copied) == n@pre &&
            Zlength(sorted) == n@pre &&
            1 <= n@pre && n@pre <= 2000 &&
            1 <= mx && mx <= 1000000000 && all == mx &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= original[k] && original[k] <= 1000000000)) &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= sorted[k] && sorted[k] <= 1000000000)) &&
            CopyMaxState(original, copied, n@pre, mx) &&
            LcmPrefixState(copied, n@pre, mx, all) &&
            Permutation(copied, sorted) &&
            IntArray::full(input@pre, n@pre, original) *
            IntArray::full(a, n@pre, sorted)
    */
    int ans = 0;
    /*@ Inv
          input == input@pre && n == n@pre && a != 0 &&
            n@pre == Zlength(original) && Zlength(copied) == n@pre &&
            Zlength(sorted) == n@pre &&
            1 <= n@pre && n@pre <= 2000 &&
            1 <= mx && mx <= 1000000000 && all == mx &&
            1 <= q && q <= 31624 &&
            0 <= ans && ans <= n@pre &&
            (q - 1) * (q - 1) <= mx &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= original[k] && original[k] <= 1000000000)) &&
            (forall k, (0 <= k && k < n@pre) =>
              (1 <= sorted[k] && sorted[k] <= 1000000000)) &&
            CopyMaxState(original, copied, n@pre, mx) &&
            LcmPrefixState(copied, n@pre, mx, all) &&
            Permutation(copied, sorted) &&
            DivisorBestState(original, mx, q, 0, ans) &&
            IntArray::full(input@pre, n@pre, original) *
            IntArray::full(a, n@pre, sorted)
    */
    for (int q = 1; (long long)q * q <= mx; ++q)
        if (mx % q == 0)
        {
            int ds[2] = {q, mx / q};
            /*@ Inv
                  input == input@pre && n == n@pre && a != 0 &&
                    n@pre == Zlength(original) && Zlength(copied) == n@pre &&
                    Zlength(sorted) == n@pre &&
                    1 <= n@pre && n@pre <= 2000 &&
                    1 <= mx && mx <= 1000000000 && all == mx &&
                    1 <= q && q <= 31623 && q * q <= mx &&
                    mx % q == 0 && 0 <= z && z <= 2 &&
                    0 <= ans && ans <= n@pre &&
                    (forall k, (0 <= k && k < n@pre) =>
                      (1 <= original[k] && original[k] <= 1000000000)) &&
                    (forall k, (0 <= k && k < n@pre) =>
                      (1 <= sorted[k] && sorted[k] <= 1000000000)) &&
                    CopyMaxState(original, copied, n@pre, mx) &&
                    LcmPrefixState(copied, n@pre, mx, all) &&
                    Permutation(copied, sorted) &&
                    DivisorBestState(original, mx, q, z, ans) &&
                    IntArray::full(input@pre, n@pre, original) *
                    IntArray::full(a, n@pre, sorted) *
                    IntArray::full(ds, 2, cons(q, cons(mx / q, nil)))
            */
            for (int z = 0; z < 2; ++z)
            {
                int d = ds[z], present = 0, count = 0;
                long long l = 1;
                /*@ Inv
                      input == input@pre && n == n@pre && a != 0 &&
                        n@pre == Zlength(original) && Zlength(copied) == n@pre &&
                        Zlength(sorted) == n@pre &&
                        1 <= n@pre && n@pre <= 2000 &&
                        1 <= mx && mx <= 1000000000 && all == mx &&
                        1 <= q && q <= 31623 && q * q <= mx &&
                        mx % q == 0 && 0 <= z && z < 2 &&
                        d == cons(q, cons(mx / q, nil))[z] &&
                        1 <= d && d <= mx &&
                        0 <= ans && ans <= n@pre &&
                        0 <= i && i <= n@pre &&
                        0 <= present && present <= 1 &&
                        0 <= count && count <= i &&
                        1 <= l && l <= d + 1 &&
                        (forall k, (0 <= k && k < n@pre) =>
                          (1 <= original[k] && original[k] <= 1000000000)) &&
                        (forall k, (0 <= k && k < n@pre) =>
                          (1 <= sorted[k] && sorted[k] <= 1000000000)) &&
                        CopyMaxState(original, copied, n@pre, mx) &&
                        LcmPrefixState(copied, n@pre, mx, all) &&
                        Permutation(copied, sorted) &&
                        DivisorBestState(original, mx, q, z, ans) &&
                        DivisorScanState(sorted, d, i, present, count, l) &&
                        IntArray::full(input@pre, n@pre, original) *
                        IntArray::full(a, n@pre, sorted) *
                        IntArray::full(ds, 2, cons(q, cons(mx / q, nil)))
                */
                for (int i = 0; i < n; ++i)
                {
                    if (a[i] == d)
                        present = 1;
                    if (d % a[i] == 0)
                    {
                        ++count;
                        l = lcm_cap(l, a[i], d);
                    }
                }
                if (!present && l == d && count > ans)
                    ans = count;
            }
        }
    /*@
          input == input@pre && n == n@pre && a != 0 &&
            n@pre == Zlength(original) &&
            Zlength(sorted) == n@pre &&
            1 <= n@pre && n@pre <= 2000 &&
            1 <= mx && mx <= 1000000000 && all == mx &&
            0 <= ans && ans <= n@pre &&
            Spec(original, ans) &&
            IntArray::full(input@pre, n@pre, original) *
            IntArray::full(a, n@pre, sorted)
    */
    free(a);
    return ans;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n;
//         scanf("%d", &n);
//         int *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i)
//             scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n));
//         free(a);
//     }
//     return 0;
// }
