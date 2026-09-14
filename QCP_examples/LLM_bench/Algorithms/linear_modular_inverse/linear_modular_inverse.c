/*
 * Compute the modular inverses of 1, ..., p - 1 in linear time.
 *
 * For a prime p and 2 <= i < p, write p = (p / i) * i + p % i.
 * Since 1 <= p % i < i, its inverse has already been computed.  Therefore
 *
 *   inverse[i] = (p - p / i) * inverse[p % i] (mod p).
 *
 * The verification contract supplies the primality and writable-array
 * assumptions.  The upper bound p <= 46340 keeps the product in signed
 * 32-bit range.
 */

/*@ Extern Coq
      (PrimeForLinearInverse : Z -> Prop)
      (ModularInversePrefix : Z -> Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_lib */

void linear_modular_inverse(int p, int *inverse)
/*@ Require
      PrimeForLinearInverse(p) &&
      2 <= p && p <= 46340 &&
      IntArray::undef_seg(inverse, 1, p)
    Ensure
      exists values,
      ModularInversePrefix(p, p, values) &&
      IntArray::seg(inverse, 1, p, values)
 */
{
    inverse[1] = 1;

    /*@ Inv Assert
          exists values,
          p == p@pre && inverse == inverse@pre &&
          PrimeForLinearInverse(p@pre) &&
          2 <= p@pre && p@pre <= 46340 &&
          2 <= i && i <= p@pre &&
          ModularInversePrefix(p@pre, i, values) &&
          IntArray::seg(inverse@pre, 1, i, values) *
          IntArray::undef_seg(inverse@pre, i, p@pre)
     */
    for (int i = 2; i < p; ++i) {
        int quotient = p / i;
        int remainder = p % i;
        /*@ Assert
              exists values,
              p == p@pre && inverse == inverse@pre &&
              PrimeForLinearInverse(p@pre) &&
              2 <= p@pre && p@pre <= 46340 &&
              2 <= i && i < p@pre &&
              quotient == p@pre / i &&
              remainder == p@pre % i &&
              p@pre == quotient * i + remainder &&
              1 <= quotient &&
              1 <= remainder && remainder < i &&
              0 < p@pre - quotient && p@pre - quotient < p@pre &&
              0 < values[remainder - 1] &&
              values[remainder - 1] < p@pre &&
              0 < (p@pre - quotient) * values[remainder - 1] &&
              (p@pre - quotient) * values[remainder - 1] <= INT_MAX &&
              ModularInversePrefix(p@pre, i, values) &&
              IntArray::seg(inverse@pre, 1, i, values) *
              IntArray::undef_seg(inverse@pre, i, p@pre)
         */
        inverse[i] = ((p - quotient) * inverse[remainder]) % p;
    }
}
