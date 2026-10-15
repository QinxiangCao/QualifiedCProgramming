/* Codeforces 435/A - Queue on Bus Stop */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P015_435A_queue_on_bus_stop.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P015_435A_queue_on_bus_stop_lib */
/*@ Extern Coq
      (GreedyPrefixState : list Z -> Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P015_435A_queue_on_bus_stop.support */
static int solver(const int *groups, int n,
                  int capacity) /* QCP_INSERT_BEGIN:P015_435A_queue_on_bus_stop.contract */

/*@ With (groups_data : list Z)
    Require
      1 <= Zlength(groups_data) && Zlength(groups_data) <= 100 &&
      1 <= capacity && capacity <= 100 &&
      (forall i, (0 <= i && i < Zlength(groups_data)) => (1 <= groups_data[i] && groups_data[i] <= capacity)) &&
      n == Zlength(groups_data) &&
      IntArray::full(groups, n, groups_data)
    Ensure
      Spec(capacity, groups_data, __return) &&
      IntArray::full(groups, n, groups_data)
*/
/* QCP_INSERT_END:P015_435A_queue_on_bus_stop.contract */

{
    int buses = 1, used = 0;
    /*@ Inv Assert
          groups == groups@pre && n == n@pre && capacity == capacity@pre &&
          1 <= Zlength(groups_data) && Zlength(groups_data) <= 100 &&
          1 <= capacity@pre && capacity@pre <= 100 &&
          (forall k, (0 <= k && k < Zlength(groups_data)) =>
             (1 <= groups_data[k] && groups_data[k] <= capacity@pre)) &&
          n@pre == Zlength(groups_data) &&
          0 <= i && i <= n@pre &&
          1 <= buses && buses <= i + 1 &&
          0 <= used && used <= capacity@pre &&
          GreedyPrefixState(sublist(0, i, groups_data), capacity@pre, buses, used) &&
          IntArray::full(groups, n@pre, groups_data)
    */
    for (int i = 0; i < n; ++i)
    {
        if (used + groups[i] > capacity)
        {
            ++buses;
            used = 0;
        }
        used += groups[i];
    }
    return buses;
}

// int main(void)
// {
//     int n, m, groups[100];
//     if (scanf("%d %d", &n, &m) != 2) return 0;
//     for (int i = 0; i < n; ++i) scanf("%d", &groups[i]);
//     printf("%d\n", solver(groups, n, m));
//     return 0;
// }
