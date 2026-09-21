/*@ Extern Coq (Zgcd: Z -> Z -> Z)
      (ModularInverse : Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib */

/*
 * The verified exgcd case supplies this interface.  In particular, x and y
 * are Bezout coefficients when the call returns.
 */
int exgcd(int a, int b, int *x, int *y)
/*@ Require
      INT_MIN < a && a <= INT_MAX &&
      INT_MIN < b && b <= INT_MAX &&
      has_int_permission(x) * has_int_permission(y)
    Ensure
      __return == Zgcd(a, b) &&
      a * (*x) + b * (*y) == Zgcd(a, b)
*/;

/*
 * Return the canonical representative of the inverse of a modulo modulus.
 * The precondition restricts this small example to the usual coprime,
 * positive inputs for which an inverse exists.
 */
int modular_inverse(int a, int modulus)
/*@ Require
      1 < modulus && 0 < a && a < modulus && Zgcd(a, modulus) == 1 && emp
    Ensure
      0 <= __return && __return < modulus &&
      ModularInverse(a, modulus, __return) && emp
*/
{
    int x;
    int y;
    int g = exgcd(a, modulus, &x, &y);

    /* The precondition and the exgcd contract imply g == 1. */
    int inverse = x % modulus;
    if (inverse < 0) {
        inverse += modulus;
    }
    return inverse;
}
