/* Codeforces 1891/A - Sorting with Twos */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P005_1891A_sorting_with_twos.support */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
      (PowerOfTwoPrefix : Z -> Z -> Prop)
      (NonPowerOfTwo : Z -> Prop)
      (SortingWithTwosPrefix : list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P005_1891A_sorting_with_twos_lib */
/* QCP_INSERT_END:P005_1891A_sorting_with_twos.support */

static int is_power_of_two(int x)
/*@ Require
      1 <= x && x <= 20 && emp
    Ensure
      (((__return == 1 && PowerOfTwoPrefix(x@pre, x@pre)) ||
        (__return == 0 && NonPowerOfTwo(x@pre))) && emp)
*/
{
    if (x <= 0) return 0;
    return (x & (x - 1)) == 0;
}

static int solver(const int *a, int n)/* QCP_INSERT_BEGIN:P005_1891A_sorting_with_twos.contract */

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 20 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (0 <= input[i] && input[i] <= 1000)) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 20)
    Ensure
      Spec(input, __return) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 20)
*/
/* QCP_INSERT_END:P005_1891A_sorting_with_twos.contract */

{
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          n == Zlength(input) &&
          1 <= n && n <= 20 &&
          (forall k, (0 <= k && k < n) =>
            (0 <= input[k] && input[k] <= 1000)) &&
          1 <= i && i <= n &&
          SortingWithTwosPrefix(input, i) &&
          IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 20)
    */
    for (int i = 1; i < n; ++i)
        if (a[i - 1] > a[i] && !is_power_of_two(i)) return 0;
    return 1;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, a[20]; scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         puts(solver(a, n) ? "YES" : "NO");
//     }
//     return 0;
// }
