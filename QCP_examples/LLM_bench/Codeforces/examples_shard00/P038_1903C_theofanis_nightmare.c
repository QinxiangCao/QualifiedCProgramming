/* Codeforces 1903/C - Theofanis' Nightmare */
// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:P038_1903C_theofanis_nightmare.support */
/*@ Extern Coq
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P038_1903C_theofanis_nightmare_lib */
/*@ Extern Coq
      (SuffixSum : list Z -> Z -> Z)
      (SuffixContributionSum : list Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P038_1903C_theofanis_nightmare.support */
static long long solver(const long long *a, int n)/* QCP_INSERT_BEGIN:P038_1903C_theofanis_nightmare.contract */

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (-100000000 <= input[i] && input[i] <= 100000000)) &&
      Int64Array::full(a, n, input)
    Ensure
      Spec(input, __return) &&
      Int64Array::full(a, n, input)
*/
/* QCP_INSERT_END:P038_1903C_theofanis_nightmare.contract */

{
    long long suffix = 0, answer = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          n@pre == Zlength(input) &&
          1 <= Zlength(input) && Zlength(input) <= 100000 &&
          (forall j, (0 <= j && j < Zlength(input)) =>
            (-100000000 <= input[j] && input[j] <= 100000000)) &&
          -1 <= i && i < n@pre &&
          -100000000 * (n@pre - i - 1) <= suffix &&
          suffix <= 100000000 * (n@pre - i - 1) &&
          -10000000000000 <= answer &&
          (0 <= i => 0 <= answer) &&
          answer <= (n@pre - i - 1) * 10000000000000 &&
          suffix == SuffixSum(input, i + 1) &&
          SuffixContributionSum(input, i + 1, answer) &&
          Int64Array::full(a, n@pre, input)
    */
    for (int i = n - 1; i >= 0; --i) {
        suffix += a[i];
        if (i == 0 || suffix > 0) answer += suffix;
    }
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); long long *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//         printf("%lld\n", solver(a, n)); free(a);
//     }
//     return 0;
// }
