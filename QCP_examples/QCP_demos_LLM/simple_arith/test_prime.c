/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib */

/*@ Extern Coq (prime : Z -> Prop)
               (HasFactorBetween : Z -> Z -> Z -> Prop)
 */

int test_prime(unsigned int x)
/*@ Require
      0 <= x && x <= 1000000000 && emp
    Ensure
      ((__return == 1 && prime(x)) ||
       (__return == 0 && (! prime(x)))) && emp
 */
{
  if (x < 2) {
    return 0;
  }

  int d;
  /*@ Inv Assert
      x == x@pre &&
      2 <= d && d <= x &&
      2 <= x@pre && x@pre <= 1000000000 &&
      (! HasFactorBetween(x@pre, 2, d))
   */
  for (d = 2; d < x; d++) {
    if (x % d == 0) {
      return 0;
    }
  }

  return 1;
}

int test_prime_sqrt(unsigned int x)
/*@ Require
      0 <= x && x <= 1000000000 && emp
    Ensure
      ((__return == 1 && prime(x)) ||
       (__return == 0 && (! prime(x)))) && emp
 */
{
  if (x < 2) {
    return 0;
  }

  int d;
  /*@ Inv Assert
      x == x@pre &&
      2 <= d && d <= 31624 &&
      2 <= x@pre && x@pre <= 1000000000 &&
      (! HasFactorBetween(x@pre, 2, d))
   */
  for (d = 2; d * d <= x; d++) {
    if (x % d == 0) {
      return 0;
    }
  }

  return 1;
}
