



/*@ Extern Coq
      (Z::divide : Z -> Z -> Prop)
      (EulerSieveResult : Z -> Z -> list Z -> list Z -> Prop)
      (Modern::PrimePrefixList : Z -> Z -> list Z -> Prop)
      (EulerInitPrefix : Z -> Z -> list Z -> Prop)
      (EulerOuterState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (EulerInnerState : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (EulerInnerMarkedState : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib */

int *get_prime(int n, int tot, int *prime)
/*@ With (prime0 : list Z)
    Require
      2 <= n && n <= 46340 &&
      Zlength(prime0) == n &&
      IntArray::seg(prime, 1, n + 1, prime0)
    Ensure
      exists prime_out final_tot,
      __return == prime@pre &&
      0 <= final_tot && final_tot <= n@pre &&
      Modern::PrimePrefixList(n@pre, final_tot, prime_out) &&
      IntArray::seg(prime@pre, 1, n@pre + 1, prime_out)
 */
{
     int flag[46341];
     /*@ Inv Assert
          exists flag_init,
          n == n@pre && prime == prime@pre && tot == tot@pre &&
          2 <= n && n <= 46340 && Zlength(prime0) == n &&
          2 <= z && z <= n + 1 && Zlength(flag_init) == z - 2 &&
          IntArray::seg(prime, 1, n + 1, prime0) *
          IntArray::undef_seg(flag, 0, 2) *
          IntArray::seg(flag, 2, z, flag_init) *
          IntArray::undef_seg(flag, z, n + 1) *
          IntArray::undef_seg(flag, n + 1, 46341)
      */
     for (int z = 2; z <= n; ++z) {
          flag[z] = 0;
     }

     tot = 0;
     /*@ Inv Assert
          exists flag_l,
          n == n@pre && prime == prime@pre &&
          tot == 0 &&
          2 <= n@pre && n@pre <= 46340 &&
          2 <= i && i <= n@pre + 1 &&
          EulerInitPrefix(n@pre, i, flag_l) &&
          (Zlength(flag_l) == n@pre - 1 &&
          Zlength(prime0) == n@pre) &&
          IntArray::seg(flag, 2, n@pre + 1, flag_l) *
          IntArray::undef_seg(flag, 0, 2) *
          IntArray::undef_seg(flag, n@pre + 1, 46341) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime0)
      */
     for (int i = 2; i <= n; i++)
		flag[i] = i;
     
     /*@ Inv Assert
          exists flag_l prime_l,
          n == n@pre && prime == prime@pre &&
          2 <= n@pre && n@pre <= 46340 &&
          2 <= i && i <= n@pre + 1 &&
          0 <= tot && tot < i &&
          EulerOuterState(n@pre, i, tot, flag_l, prime_l) &&
          (Zlength(flag_l) == n@pre - 1 &&
          Zlength(prime_l) == n@pre) &&
          IntArray::seg(flag, 2, n@pre + 1, flag_l) *
          IntArray::undef_seg(flag, 0, 2) *
          IntArray::undef_seg(flag, n@pre + 1, 46341) *
          IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
      */
	for (int i = 2; i <= n; i++) {
		if (flag[i] == i) {
               tot = tot + 1;
               prime[tot] = i;
          }
          
          /*@ Inv Assert
               exists flag_l prime_l,
               n == n@pre && prime == prime@pre &&
               2 <= n@pre && n@pre <= 46340 &&
               2 <= i && i <= n@pre &&
               1 <= tot && tot <= n@pre &&
               1 <= j && j <= tot &&
               EulerInnerState(n@pre, i, j, tot, flag_l, prime_l) &&
               2 <= prime_l[j - 1] && prime_l[j - 1] <= i &&
               (Zlength(flag_l) == n@pre - 1 &&
          Zlength(prime_l) == n@pre &&
          tot < i + 1) &&
          IntArray::seg(flag, 2, n@pre + 1, flag_l) *
          IntArray::undef_seg(flag, 0, 2) *
          IntArray::undef_seg(flag, n@pre + 1, 46341) *
               IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
           */
		for (int j = 1; i * prime[j] <= n && j <= tot; j++) {
			flag[i * prime[j]] = prime[j];
               /*@ Assert
                    exists flag_l prime_l,
                    n == n@pre && prime == prime@pre &&
                    2 <= n@pre && n@pre <= 46340 &&
                    2 <= i && i <= n@pre &&
                    1 <= tot && tot <= n@pre &&
                    1 <= j && j <= tot &&
                    i * prime_l[j - 1] <= n@pre &&
                    EulerInnerMarkedState(n@pre, i, j, tot, flag_l, prime_l) &&
                    2 <= prime_l[j - 1] && prime_l[j - 1] <= i &&
                    (Zlength(flag_l) == n@pre - 1 &&
          Zlength(prime_l) == n@pre &&
          tot < i + 1 &&
          (!Z::divide(prime_l[j - 1], i) => j + 1 <= tot)) &&
          IntArray::seg(flag, 2, n@pre + 1, flag_l) *
          IntArray::undef_seg(flag, 0, 2) *
          IntArray::undef_seg(flag, n@pre + 1, 46341) *
                    IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
                */
			if (i % prime[j] == 0) {
                    /*@ Assert
                         exists flag_l prime_l,
                         n == n@pre && prime == prime@pre &&
                         2 <= n@pre && n@pre <= 46340 &&
                         2 <= i && i <= n@pre &&
                         1 <= tot && tot <= n@pre &&
                         1 <= j && j <= tot &&
                         2 <= prime_l[j - 1] && prime_l[j - 1] <= i &&
                         EulerOuterState(n@pre, i + 1, tot, flag_l, prime_l) &&
                         (Zlength(flag_l) == n@pre - 1 &&
          Zlength(prime_l) == n@pre &&
          2 <= i + 1 &&
          i + 1 <= n@pre + 1 &&
          0 <= tot &&
          tot < i + 1) &&
          IntArray::seg(flag, 2, n@pre + 1, flag_l) *
          IntArray::undef_seg(flag, 0, 2) *
          IntArray::undef_seg(flag, n@pre + 1, 46341) *
                         IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
                     */
                    break;
               }
               /*@ Assert
                    exists flag_l prime_l,
                    n == n@pre && prime == prime@pre &&
                    2 <= n@pre && n@pre <= 46340 &&
                    2 <= i && i <= n@pre &&
                    1 <= tot && tot <= n@pre &&
                    1 <= j + 1 && j + 1 <= tot &&
                    EulerInnerState(n@pre, i, j + 1, tot, flag_l, prime_l) &&
                    2 <= prime_l[j] && prime_l[j] <= i &&
                    (Zlength(flag_l) == n@pre - 1 &&
          Zlength(prime_l) == n@pre &&
          tot < i + 1) &&
          IntArray::seg(flag, 2, n@pre + 1, flag_l) *
          IntArray::undef_seg(flag, 0, 2) *
          IntArray::undef_seg(flag, n@pre + 1, 46341) *
                    IntArray::seg(prime@pre, 1, n@pre + 1, prime_l)
                */
		}

	}
     
     
     /*@ Assert
          exists flag_out prime_out,
          n == n@pre && prime == prime@pre &&
          0 <= tot && tot <= n &&
          EulerSieveResult(n, tot, flag_out, prime_out) &&
          IntArray::seg(prime, 1, n + 1, prime_out) *
          IntArray::undef_full(flag, 46341)
      */
     return prime;
}
