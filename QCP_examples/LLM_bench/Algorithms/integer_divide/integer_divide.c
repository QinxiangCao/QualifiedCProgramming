/*@ Extern Coq
      (PrimeFactorization : Z -> list Z -> Prop)
      (FactorizationProgress : Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_lib */

void divide(int n, int *p)
/*@ With (original : Z)
    Require
      n == original &&
      1 <= original && original <= INT_MAX &&
      IntArray::undef_full(p, original)
    Ensure
      exists factors,
      PrimeFactorization(original, factors) &&
      IntArray::undef_seg(p, 0, 1) *
      IntArray::seg(p, 1, 1 + Zlength(factors), factors) *
      IntArray::undef_seg(p, 1 + Zlength(factors), original)
 */
{
	int cnt = 0;
	/*@ Inv Assert
	    exists factors,
	    p == p@pre &&
	    1 <= original && original <= INT_MAX &&
	    1 <= n && n <= original &&
	    2 <= i && i <= INT_MAX && i <= original + 1 &&
	    0 <= cnt && cnt < original &&
	    Zlength(factors) == cnt &&
	    FactorizationProgress(original, factors, n, i) &&
	    IntArray::undef_seg(p@pre, 0, 1) *
	    IntArray::seg(p@pre, 1, 1 + cnt, factors) *
	    IntArray::undef_seg(p@pre, 1 + cnt, original)
	 */
	for (int i = 2; i <= n; i++) {
		/*@ Inv Assert
		    exists factors,
		    p == p@pre &&
		    1 <= original && original <= INT_MAX &&
		    1 <= n && n <= original &&
		    2 <= i && i <= original &&
		    (n == 1 || i <= n) &&
		    0 <= cnt && cnt < original &&
		    Zlength(factors) == cnt &&
		    FactorizationProgress(original, factors, n, i) &&
		    IntArray::undef_seg(p@pre, 0, 1) *
		    IntArray::seg(p@pre, 1, 1 + cnt, factors) *
		    IntArray::undef_seg(p@pre, 1 + cnt, original)
		 */
		while (n % i == 0) {
			/*@ cnt + 1 < original by local */
			cnt++;
			p[cnt] = i;
			n /= i;
		}
		if (n == 1) {
			break;
		}
		/*@ i < INT_MAX by local */
	}
}
