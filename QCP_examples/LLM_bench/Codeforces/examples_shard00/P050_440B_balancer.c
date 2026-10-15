/* Codeforces 440/B - Balancer */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P050_440B_balancer.support */
/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P050_440B_balancer_lib */
/*@ Extern Coq
      (ListLib::sum : list Z -> Z)
      (PrefixImbalance : list Z -> Z -> Z)
      (PrefixTransportCost : list Z -> Z -> Z)
*/
/* QCP_INSERT_END:P050_440B_balancer.support */
static long long solver(const long long *a, int n)/* QCP_INSERT_BEGIN:P050_440B_balancer.contract */

/*@ With (values : list Z)
    Require
      1 <= Zlength(values) && Zlength(values) <= 50000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (0 <= values[i] && values[i] <= 1000000000)) &&
      Pre(values) &&
      n == Zlength(values) &&
      Int64Array::full(a, n, values)
    Ensure
      Spec(values, __return) &&
      Int64Array::full(a, n, values)
*/
/* QCP_INSERT_END:P050_440B_balancer.contract */

{
    long long sum = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 50000 &&
          Zlength(values) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 <= values[k] && values[k] <= 1000000000)) &&
          Pre(values) &&
          0 <= i && i <= n@pre &&
          sum == ListLib::sum(sublist(0, i, values)) &&
          0 <= sum && sum <= 1000000000 * i &&
          Int64Array::full(a@pre, n@pre, values)
    */
    for (int i = 0; i < n; ++i) sum += a[i];
    long long target = sum / n, balance = 0, answer = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 50000 &&
          Zlength(values) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 <= values[k] && values[k] <= 1000000000)) &&
          Pre(values) &&
          sum == ListLib::sum(values) &&
          0 <= sum && sum <= 1000000000 * n@pre &&
          target == ListLib::sum(values) / n@pre &&
          0 <= target && target <= 1000000000 &&
          0 <= i && i <= n@pre - 1 &&
          balance == PrefixImbalance(values, i) &&
          -1000000000 * i <= balance && balance <= 1000000000 * i &&
          answer == PrefixTransportCost(values, i) &&
          0 <= answer && answer <= 1000000000 * i * i &&
          Int64Array::full(a@pre, n@pre, values)
    */
    for (int i = 0; i + 1 < n; ++i) {
        balance += a[i] - target;
        answer += balance < 0 ? -balance : balance;
    }
    return answer;
}

// int main(void)
// {
//     int n; if (scanf("%d", &n) != 1) return 0;
//     long long a[50000]; for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//     printf("%lld\n", solver(a, n));
//     return 0;
// }
