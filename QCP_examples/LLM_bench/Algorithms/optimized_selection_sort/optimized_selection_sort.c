/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq
      (optimized_selection_sort_result : list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib */

void optimized_selection_sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(input) == n &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        optimized_selection_sort_result(input, output) &&
        Permutation(input, output) &&
        increasing(output) &&
        Zlength(output) == n &&
        IntArray::full(a, n, output)
 */
{
    int i;

    /*@ Inv Assert
        exists cur,
          a == a@pre && n == n@pre &&
          0 <= n && n <= INT_MAX &&
          Zlength(input) == n && Zlength(cur) == n &&
          0 <= i && i <= n && i < INT_MAX &&
          Permutation(input, cur) &&
          increasing(sublist(0, i, cur)) &&
          (forall (p : Z) (q : Z),
             (0 <= p && p < i && i <= q && q < n) =>
             (Znth(p, cur, 0) <= Znth(q, cur, 0))) &&
          IntArray::full(a, n, cur)
        by array_length
    */
    for (i = 0; i + 1 < n; ++i) {
        int min_index = i;
        int j;

        /*@ Inv Assert
            exists cur,
              a == a@pre && n == n@pre &&
              0 <= n && n <= INT_MAX &&
              Zlength(input) == n && Zlength(cur) == n &&
              0 <= i && i + 1 < n &&
              i <= min_index && min_index < j &&
              i + 1 <= j && j <= n &&
              Permutation(input, cur) &&
              increasing(sublist(0, i, cur)) &&
              (forall (p : Z) (q : Z),
                 (0 <= p && p < i && i <= q && q < n) =>
                 (Znth(p, cur, 0) <= Znth(q, cur, 0))) &&
              (forall (q : Z),
                 (i <= q && q < j) =>
                 (Znth(min_index, cur, 0) <= Znth(q, cur, 0))) &&
              IntArray::full(a, n, cur)
            by array_length
        */
        for (j = i + 1; j < n; ++j) {
            if (a[j] < a[min_index]) {
                min_index = j;
            }
        }

        /* Avoid the three writes when the current element is already minimal. */
        if (min_index != i) {
            int tmp = a[i];
            a[i] = a[min_index];
            a[min_index] = tmp;
        }
    }
}
