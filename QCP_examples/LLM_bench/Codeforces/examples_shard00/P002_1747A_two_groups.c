/* Codeforces 1747/A - Two Groups */
// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:P002_1747A_two_groups.support */
/*@ Extern Coq
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
      (ListLib::sum : list Z -> Z)
      (Z::abs : Z -> Z)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P002_1747A_two_groups_lib */
/* QCP_INSERT_END:P002_1747A_two_groups.support */

static long long llabs(long long x)
/*@ Require
      -100000000000000 <= x && x <= 100000000000000 && emp
    Ensure
      __return == Z::abs(x@pre) && emp
*/
{
    return x < 0 ? -x : x;
}


static long long solver(const long long *a, int n)
/* QCP_INSERT_BEGIN:P002_1747A_two_groups.contract */
/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (-1000000000 <= input[i] && input[i] <= 1000000000)) &&
      Int64Array::full(a, n, input) *
      Int64Array::undef_seg(a, n, 100005)
    Ensure
      Spec(input, __return) &&
      Int64Array::full(a, n, input) *
      Int64Array::undef_seg(a, n, 100005)
*/
/* QCP_INSERT_END:P002_1747A_two_groups.contract */

{
    long long sum = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(input) == n@pre &&
          (forall (k : Z), (0 <= k && k < n@pre) =>
            -1000000000 <= input[k] && input[k] <= 1000000000) &&
          0 <= i && i <= n@pre &&
          sum == ListLib::sum(sublist(0, i, input)) &&
          -1000000000 * i <= sum && sum <= 1000000000 * i &&
          Int64Array::full(a@pre, n@pre, input) *
          Int64Array::undef_seg(a@pre, n@pre, 100005)
     */
    for (int i = 0; i < n; ++i) sum += a[i];
    return llabs(sum);
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1) return 0;
//     while (t--) {
//         int n; long long a[100005];
//         scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//         printf("%lld\n", solver(a, n));
//     }
//     return 0;
// }
