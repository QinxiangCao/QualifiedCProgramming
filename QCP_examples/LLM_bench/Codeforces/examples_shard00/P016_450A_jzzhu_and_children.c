/* Codeforces 450/A - Jzzhu and Children */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P016_450A_jzzhu_and_children.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P016_450A_jzzhu_and_children_lib */
/* QCP_INSERT_END:P016_450A_jzzhu_and_children.support */

/*@ Extern Coq
      (LastMaxPrefix : Z -> list Z -> Z -> Z -> Z -> Prop)
*/
static int solver(const int *wants, int n,
                  int m) /* QCP_INSERT_BEGIN:P016_450A_jzzhu_and_children.contract */

/*@ With (wants_data : list Z)
    Require
      1 <= Zlength(wants_data) && Zlength(wants_data) <= 100 &&
      1 <= m && m <= 100 &&
      (forall i, (0 <= i && i < Zlength(wants_data)) => (1 <= wants_data[i] && wants_data[i] <= 100)) &&
      n == Zlength(wants_data) &&
      IntArray::full(wants, n, wants_data)
    Ensure
      Spec(m, wants_data, __return) &&
      IntArray::full(wants, n, wants_data)
*/
/* QCP_INSERT_END:P016_450A_jzzhu_and_children.contract */

{
    int answer = 1, best = 0;
    /*@ Inv Assert
          wants == wants@pre && n == n@pre && m == m@pre &&
          1 <= Zlength(wants_data) && Zlength(wants_data) <= 100 &&
          1 <= m && m <= 100 &&
          (forall j, (0 <= j && j < Zlength(wants_data)) =>
             (1 <= wants_data[j] && wants_data[j] <= 100)) &&
          n == Zlength(wants_data) &&
          0 <= i && i <= n &&
          LastMaxPrefix(m, wants_data, i, best, answer) &&
          IntArray::full(wants, n, wants_data)
    */
    for (int i = 0; i < n; ++i)
    {
        int turns = (wants[i] + m - 1) / m;
        if (turns >= best)
        {
            best = turns;
            answer = i + 1;
        }
    }
    return answer;
}

// int main(void)
// {
//     int n, m, wants[100];
//     if (scanf("%d %d", &n, &m) != 2) return 0;
//     for (int i = 0; i < n; ++i) scanf("%d", &wants[i]);
//     printf("%d\n", solver(wants, n, m));
//     return 0;
// }
