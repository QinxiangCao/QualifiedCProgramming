



/*@ Extern Coq
      (EulerSieveResult : Z -> Z -> list Z -> list Z -> Prop)
      (EulerInitPrefix : Z -> Z -> list Z -> Prop)
      (EulerOuterState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (EulerInnerState : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (EulerInnerMarkedState : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib */

int *get_prime(int n, int tot, int *flag, int *prime)
/*@ With (flag0 : list Z) (prime0 : list Z)
    Require
      2 <= n && n <= 46340 &&
      Zlength(flag0) == n - 1 &&
      Zlength(prime0) == n &&
      IntArray::seg(flag, 2, n + 1, flag0) *
      IntArray::seg(prime, 1, n + 1, prime0)
    Ensure
      exists flag_out prime_out final_tot,
      __return == prime@pre &&
      EulerSieveResult(n@pre, final_tot, flag_out, prime_out) &&
      IntArray::seg(flag@pre, 2, n@pre + 1, flag_out) *
      IntArray::seg(prime@pre, 1, n@pre + 1, prime_out)
 */
{
	tot = 0;
     /*@ Inv Assert
          exists flag_l,
          n == n@pre && flag == flag@pre && prime == prime@pre &&
          tot == 0 &&
          2 <= n@pre && n@pre <= 46340 &&
          2 <= i && i <= n@pre + 1 &&
          EulerInitPrefix(n@pre, i, flag_l) &&
          IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime0)
      */
     for (int i = 2; i <= n; i++)
		flag[i] = i;
     /*@ Assert
          exists flag_l,
          n == n@pre && flag == flag@pre && prime == prime@pre &&
          tot == 0 &&
          2 <= n@pre && n@pre <= 46340 &&
          EulerOuterState(n@pre, 2, tot, flag_l, prime0) &&
          IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime0)
      */
     /*@ Inv Assert
          exists flag_l prime_l,
          n == n@pre && flag == flag@pre && prime == prime@pre &&
          2 <= n@pre && n@pre <= 46340 &&
          2 <= i && i <= n@pre + 1 &&
          0 <= tot && tot < i &&
          EulerOuterState(n@pre, i, tot, flag_l, prime_l) &&
          IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
      */
	for (int i = 2; i <= n; i++) {
		if (flag[i] == i) {
               tot = tot + 1;
               prime[tot] = i;
          }
          /*@ Assert
               exists flag_l prime_l,
               n == n@pre && flag == flag@pre && prime == prime@pre &&
               2 <= n@pre && n@pre <= 46340 &&
               2 <= i && i <= n@pre &&
               1 <= tot && tot <= n@pre &&
               EulerInnerState(n@pre, i, 1, tot, flag_l, prime_l) &&
               2 <= prime_l[0] && prime_l[0] <= i &&
               i * prime_l[0] <= INT_MAX &&
               IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
               IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
           */
          /*@ Inv Assert
               exists flag_l prime_l,
               n == n@pre && flag == flag@pre && prime == prime@pre &&
               2 <= n@pre && n@pre <= 46340 &&
               2 <= i && i <= n@pre &&
               1 <= tot && tot <= n@pre &&
               1 <= j && j <= tot &&
               EulerInnerState(n@pre, i, j, tot, flag_l, prime_l) &&
               2 <= prime_l[j - 1] && prime_l[j - 1] <= i &&
               i * prime_l[j - 1] <= INT_MAX &&
               IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
               IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
           */
		for (int j = 1; i * prime[j] <= n && j <= tot; j++) {
			flag[i * prime[j]] = prime[j];
               /*@ Assert
                    exists flag_l prime_l,
                    n == n@pre && flag == flag@pre && prime == prime@pre &&
                    2 <= n@pre && n@pre <= 46340 &&
                    2 <= i && i <= n@pre &&
                    1 <= tot && tot <= n@pre &&
                    1 <= j && j <= tot &&
                    i * prime_l[j - 1] <= n@pre &&
                    EulerInnerMarkedState(n@pre, i, j, tot, flag_l, prime_l) &&
                    2 <= prime_l[j - 1] && prime_l[j - 1] <= i &&
                    IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
                    IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
                */
			if (i % prime[j] == 0) {
                    /*@ Assert
                         exists flag_l prime_l,
                         n == n@pre && flag == flag@pre && prime == prime@pre &&
                         2 <= n@pre && n@pre <= 46340 &&
                         2 <= i && i <= n@pre &&
                         1 <= tot && tot <= n@pre &&
                         1 <= j && j <= tot &&
                         2 <= prime_l[j - 1] && prime_l[j - 1] <= i &&
                         EulerOuterState(n@pre, i + 1, tot, flag_l, prime_l) &&
                         IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
                         IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
                     */
                    break;
               }
               /*@ Assert
                    exists flag_l prime_l,
                    n == n@pre && flag == flag@pre && prime == prime@pre &&
                    2 <= n@pre && n@pre <= 46340 &&
                    2 <= i && i <= n@pre &&
                    1 <= tot && tot <= n@pre &&
                    1 <= j + 1 && j + 1 <= tot &&
                    EulerInnerState(n@pre, i, j + 1, tot, flag_l, prime_l) &&
                    2 <= prime_l[j] && prime_l[j] <= i &&
                    i * prime_l[j] <= INT_MAX &&
                    IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
                    IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
                */
		}
          /*@ Assert
               exists flag_l prime_l,
               n == n@pre && flag == flag@pre && prime == prime@pre &&
               2 <= n@pre && n@pre <= 46340 &&
               2 <= i && i <= n@pre &&
               0 <= tot && tot < i + 1 &&
               EulerOuterState(n@pre, i + 1, tot, flag_l, prime_l) &&
               IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
               IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
           */
	}
     /*@ Assert
          exists flag_l prime_l,
          n == n@pre && flag == flag@pre && prime == prime@pre &&
          2 <= n@pre && n@pre <= 46340 &&
          0 <= tot && tot <= n@pre &&
          EulerOuterState(n@pre, n@pre + 1, tot, flag_l, prime_l) &&
          IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
      */
     /*@ exists flag_l prime_l,
          n == n@pre && flag == flag@pre && prime == prime@pre &&
          2 <= n@pre && n@pre <= 46340 &&
          0 <= tot && tot <= n@pre &&
          EulerOuterState(n@pre, n@pre + 1, tot, flag_l, prime_l) &&
          IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
         which implies
         exists flag_l prime_l,
          n == n@pre && flag == flag@pre && prime == prime@pre &&
          2 <= n@pre && n@pre <= 46340 &&
          0 <= tot && tot <= n@pre &&
          EulerSieveResult(n@pre, tot, flag_l, prime_l) &&
          IntArray::seg(flag@pre, 2, n@pre + 1, flag_l) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
      */
     return prime;
}
