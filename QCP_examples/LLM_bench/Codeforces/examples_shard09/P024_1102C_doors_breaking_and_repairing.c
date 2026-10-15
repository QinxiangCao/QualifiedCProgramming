/*
 * Codeforces 1102/C - Doors Breaking and Repairing  (rating 1200, GAMES)
 *
 * If x > y every door falls: you always out-damage the repair.  Otherwise only
 * doors with a_i <= x can ever be zeroed (one hit), and Slavik protects one
 * such door after each of your breaks, so you get every other one: the answer
 * is ceil(cnt / 2) where cnt counts doors with a_i <= x.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> list Z -> Z -> Prop)
*/
/*@ Extern Coq (WeakDoorCount : Z -> list Z -> Z) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P024_1102C_doors_breaking_and_repairing_lib */


/* solver: pure.  Number of doors ending at durability 0 under optimal play. */
static int solver(const int *a, int n, int x, int y)
/* QCP_INSERT_BEGIN:shard09-P024-solver-contract */
/*@ With (durability : list Z)
    Require
      1 <= x && x <= 100000 && 1 <= y && y <= 100000 &&
      1 <= n && n <= 100 && 
      (forall i, (0 <= i && i < n) => (1 <= durability[i] && durability[i] <= 100000)) &&
      n == Zlength(durability) && IntArray::full(a, n, durability)
    Ensure
      Spec(x, y, durability, __return) &&
      IntArray::full(a, n, durability)
*/
/* QCP_INSERT_END:shard09-P024-solver-contract */
{
    if (x > y)
        return n;
    int cnt = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre && x == x@pre && y == y@pre &&
          1 <= x && x <= 100000 && 1 <= y && y <= 100000 &&
          1 <= n && n <= 100 &&
          (forall j, (0 <= j && j < n) =>
            (1 <= durability[j] && durability[j] <= 100000)) &&
          n == Zlength(durability) && x <= y &&
          0 <= i && i <= n && 0 <= cnt && cnt <= i &&
          cnt == WeakDoorCount(x, sublist(0, i, durability)) &&
          IntArray::full(a, n, durability)
    */
    for (int i = 0; i < n; i++)
        if (a[i] <= x)
            cnt++;
    return (cnt + 1) / 2;
}

// int main(void)
// {
//     int n, x, y;
//     if (scanf("%d %d %d", &n, &x, &y) != 3)
//         return 0;
//     static int a[105];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%d\n", solver(a, n, x, y));
//     return 0;
// }
