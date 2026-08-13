



/*@ Extern Coq
      (StrictPrime : Z -> Prop)
      (PrimeIndicatorList : Z -> list Z -> Prop)
      (SieveInitPrefix : Z -> Z -> list Z -> Prop)
      (SieveStage : Z -> Z -> list Z -> Prop)
      (SieveMarkState : Z -> Z -> Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_lib */

void solve(int n, int *f)
/*@ With (initial : list Z)
    Require
      2 <= n && n <= 1000000000 &&
      Zlength(initial) == n &&
      IntArray::seg(f, 1, n + 1, initial)
    Ensure
      exists result,
      PrimeIndicatorList(n, result) &&
      IntArray::seg(f, 1, n + 1, result)
 */
{
    /*@ Inv Assert
          exists current,
          f == f@pre && n == n@pre &&
          2 <= n@pre && n@pre <= 1000000000 &&
          1 <= i && i <= n@pre + 1 &&
          SieveInitPrefix(n@pre, i, current) &&
          IntArray::seg(f@pre, 1, n@pre + 1, current)
     */
    for (int i = 1; i <= n; i++) {
        f[i] = 1;
    }
    f[1] = 0;
    f[2] = 1;

    /*@ Assert
          exists current,
          f == f@pre && n == n@pre &&
          2 <= n@pre && n@pre <= 1000000000 &&
          SieveStage(n@pre, 2, current) &&
          IntArray::seg(f@pre, 1, n@pre + 1, current)
     */

    /*@ Inv Assert
          exists current,
          f == f@pre && n == n@pre &&
          2 <= n@pre && n@pre <= 1000000000 &&
          2 <= i && i <= n@pre + 1 &&
          SieveStage(n@pre, i, current) &&
          IntArray::seg(f@pre, 1, n@pre + 1, current)
     */
    for (int i = 2; i <= n; i++) {
        if (f[i] == 1) {
            /*@ Inv Assert
                  exists current,
                  f == f@pre && n == n@pre &&
                  2 <= n@pre && n@pre <= 1000000000 &&
                  2 <= i && i <= n@pre &&
                  2 * i <= j && j <= n@pre + i &&
                  SieveMarkState(n@pre, i, j, current) &&
                  IntArray::seg(f@pre, 1, n@pre + 1, current)
             */
            for (int j = i * 2; j <= n; j = j + i) {
                f[j] = 0;
            }

            /*@ Assert
                  exists current,
                  f == f@pre && n == n@pre &&
                  2 <= n@pre && n@pre <= 1000000000 &&
                  2 <= i && i <= n@pre &&
                  SieveStage(n@pre, i + 1, current) &&
                  IntArray::seg(f@pre, 1, n@pre + 1, current)
             */
        }

        /*@ Assert
              exists current,
              f == f@pre && n == n@pre &&
              2 <= n@pre && n@pre <= 1000000000 &&
              2 <= i && i <= n@pre &&
              SieveStage(n@pre, i + 1, current) &&
              IntArray::seg(f@pre, 1, n@pre + 1, current)
         */
    }

    /*@ Assert
          exists result,
          f == f@pre && n == n@pre &&
          PrimeIndicatorList(n@pre, result) &&
          IntArray::seg(f@pre, 1, n@pre + 1, result)
     */
}
