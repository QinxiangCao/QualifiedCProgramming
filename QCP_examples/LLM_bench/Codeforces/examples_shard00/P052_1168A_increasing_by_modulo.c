/* Codeforces 1168/A - Increasing by Modulo */
// #include <stdio.h>
// #include <stdlib.h>

static int n, m, *a;

/* QCP_INSERT_BEGIN:P052_1168A_increasing_by_modulo.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (Feasible : Z -> list Z -> Z -> Prop)
      (GreedyPrefixState : Z -> list Z -> Z -> Z -> Z -> Prop)
      (SearchState : Z -> list Z -> Z -> Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P052_1168A_increasing_by_modulo_lib */
/* QCP_INSERT_END:P052_1168A_increasing_by_modulo.support */

static int feasible(int x)
/*@ With (nv mv arr : Z)
             (values : list Z)
    Require
      1 <= mv && mv <= 300000 &&
      1 <= nv && nv <= 300000 &&
      0 <= x && x < mv &&
      Zlength(values) == nv &&
      (forall j, (0 <= j && j < nv) =>
        (0 <= values[j] && values[j] < mv)) &&
      store(&n, int, nv) *
      store(&m, int, mv) *
      store(&a, int *, arr) *
      IntArray::full(arr, nv, values)
    Ensure
      0 <= __return && __return <= 1 &&
      (__return != 0 <=> Feasible(mv, values, x)) &&
      store(&n, int, nv) *
      store(&m, int, mv) *
      store(&a, int *, arr) *
      IntArray::full(arr, nv, values)
*/
{
    int last = 0;

    /*@ Inv Assert
          x == x@pre &&
          1 <= mv && mv <= 300000 &&
          1 <= nv && nv <= 300000 &&
          0 <= x@pre && x@pre < mv &&
          Zlength(values) == nv &&
          0 <= i && i <= nv &&
          (forall j, (0 <= j && j < nv) =>
            (0 <= values[j] && values[j] < mv)) &&
          GreedyPrefixState(mv, values, x@pre, i, last) &&
          store(&n, int, nv) *
          store(&m, int, mv) *
          store(&a, int *, arr) *
          IntArray::full(arr, nv, values)
    */
    for (int i = 0; i < n; ++i) {
        if (a[i] + x < m) {
            if (a[i] + x < last) {
                return 0;
            }
            if (a[i] > last) {
                last = a[i];
            }
        } else {
            int wrapped = (a[i] + x) % m;

            if (a[i] > last && wrapped < last) {
                last = a[i];
            }
        }
    }

    return 1;
}

static int solver(int nn, int mm, const int *input) /* QCP_INSERT_BEGIN:P052_1168A_increasing_by_modulo.contract */

/*@ With (modulus : Z)
             (values : list Z)
             (n_before m_before a_before : Z)
    Require
      1 <= modulus && modulus <= 300000 &&
      1 <= Zlength(values) && Zlength(values) <= 300000 &&
      (forall i, (0 <= i && i < Zlength(values)) =>
        (0 <= values[i] && values[i] < modulus)) &&
      nn == Zlength(values) && mm == modulus &&
      IntArray::full(input, nn, values) *
      store(&n, int, n_before) *
      store(&m, int, m_before) *
      store(&a, int *, a_before)
    Ensure
      Spec(modulus, values, __return) &&
      IntArray::full(input, nn, values) *
      store(&n, int, nn) *
      store(&m, int, mm) *
      store(&a, int *, 0)
*/
/* QCP_INSERT_END:P052_1168A_increasing_by_modulo.contract */

{
    n = nn;
    m = mm;
    a = (int *)input;

    int lo = 0;
    int hi = m - 1;
    int ans = hi;

    /*@ Inv Assert
          nn == nn@pre && mm == mm@pre && input == input@pre &&
          nn@pre == Zlength(values) && mm@pre == modulus &&
          1 <= modulus && modulus <= 300000 &&
          1 <= Zlength(values) && Zlength(values) <= 300000 &&
          0 <= lo && lo <= modulus &&
          -1 <= hi && hi < modulus &&
          lo <= hi + 1 &&
          0 <= ans && ans < modulus &&
          (forall i, (0 <= i && i < Zlength(values)) =>
            (0 <= values[i] && values[i] < modulus)) &&
          SearchState(modulus, values, lo, hi, ans) &&
          IntArray::full(input, nn@pre, values) *
          store(&n, int, nn@pre) *
          store(&m, int, mm@pre) *
          store(&a, int *, input)
    */
    while (lo <= hi) {
        int mid = (lo + hi) / 2;

        if (feasible(mid) /*@ where nv = nn@pre, mv = modulus,
                                     arr = input, values = values */) {
            ans = mid;
            hi = mid - 1;
        } else {
            lo = mid + 1;
        }
    }

    a = 0;
    return ans;
}

// int main(void)
// {
//     if (scanf("%d %d", &n, &m) != 2) {
//         return 0;
//     }
//
//     a = malloc((size_t)n * sizeof(*a));
//     for (int i = 0; i < n; ++i) {
//         scanf("%d", &a[i]);
//     }
//
//     int *out = a;
//     printf("%d\n", solver(n, m, out));
//     free(out);
//     return 0;
// }
