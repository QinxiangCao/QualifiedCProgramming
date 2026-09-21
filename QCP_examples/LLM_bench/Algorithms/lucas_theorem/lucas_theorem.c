/*
 * Compute C(n + m, n) modulo a prime p with Lucas' theorem.
 *
 * The problem guarantees
 *
 *   1 <= n, m, p <= 100000
 *
 * and that p is prime.  Products use long long and are reduced modulo p
 * before conversion to int, covering the full problem modulus range.
 *
 * Input/output handling is intentionally left to the caller.  The function
 * lucas_theorem is the algorithmic entry point for one test case.
 */

/*@ Extern Coq
      (Z::min : Z -> Z -> Z)
      (Z::modulo : Z -> Z -> Z)
      (ModularPower : Z -> Z -> Z -> Z -> Prop)
      (PrimeForLucas : Z -> Prop)
      (LucasBinomialCoefficient : Z -> Z -> Z)
      (BinomialDigitResidue : Z -> Z -> Z -> Z -> Prop)
      (LucasBinomialResidue : Z -> Z -> Z -> Z -> Prop)
      (DigitNumeratorPrefix : Z -> Z -> Z -> Z)
      (DigitDenominatorPrefix : Z -> Z)
      (LucasDigit : Z -> Z -> Z -> Z)
      (LucasPrefixProduct : Z -> Z -> Z -> Z -> Z)
      (DigitProductProgress : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (LucasProgress : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_lib */

int modular_power(int base, int exponent, int modulus)
/*@ Require
      0 <= base && base < modulus &&
      0 <= exponent && 2 <= modulus && modulus <= 100000 && emp
    Ensure ModularPower(base, exponent, modulus, __return) && emp
 */;

/* Compute C(upper, lower) modulo prime, using the symmetric smaller lower. */
int binomial_digit_mod_prime(int upper, int lower, int prime)
/*@ Require
      PrimeForLucas(prime) &&
      0 <= lower && lower <= upper && upper < prime &&
      2 <= prime && prime <= 100000 &&
      emp
    Ensure
      BinomialDigitResidue(upper@pre, lower@pre, prime@pre, __return) && emp
 */
{
    if (lower > upper) {
        return 0;
    }

    if (lower > upper - lower) {
        lower = upper - lower;
    }

    int numerator = 1;
    int denominator = 1;

    /*@ Inv Assert
          upper == upper@pre && prime == prime@pre &&
          PrimeForLucas(prime) &&
          0 <= lower@pre && lower@pre <= upper && upper < prime &&
          2 <= prime && prime <= 100000 &&
          lower == Z::min(lower@pre, upper - lower@pre) &&
          0 <= lower && lower <= upper - lower &&
          1 <= i && i <= lower + 1 &&
          0 <= numerator && numerator < prime &&
          0 <= denominator && denominator < prime &&
          DigitProductProgress(upper, lower, prime,
            i, numerator, denominator) && emp
     */
    for (int i = 1; i <= lower; ++i) {
        int factor = upper - lower + i;
        long long numerator_product = (long long)numerator * factor;
        long long denominator_product = (long long)denominator * i;

        numerator = (int)(numerator_product % prime);
        denominator = (int)(denominator_product % prime);
    }

    int inverse = modular_power(denominator, prime - 2, prime);
    long long answer = (long long)numerator * inverse;
    return (int)(answer % prime);
}

int lucas_theorem(int n, int m, int prime)
/*@ Require
      1 <= n && n <= 100000 &&
      1 <= m && m <= 100000 &&
      2 <= prime && prime <= 100000 &&
      PrimeForLucas(prime) &&
      emp
    Ensure
      LucasBinomialResidue(n@pre, m@pre, prime@pre, __return) && emp
 */
{
    int upper = n + m;
    int lower = n;
    int result = 1;

    /*@ Inv Assert
          n == n@pre && m == m@pre && prime == prime@pre &&
          0 <= n && 0 <= m &&
          2 <= prime && prime <= 100000 &&
          PrimeForLucas(prime) &&
          0 <= lower && lower <= upper &&
          0 <= result && result < prime &&
          LucasProgress(n + m, n, prime, upper, lower, result) && emp
     */
    while (upper > 0 || lower > 0) {
        int upper_digit = upper % prime;
        int lower_digit = lower % prime;

        if (lower_digit > upper_digit) {
            return 0;
        }

        int digit_binomial =
            binomial_digit_mod_prime(upper_digit, lower_digit, prime);
        long long product = (long long)result * digit_binomial;
        result = (int)(product % prime);

        upper /= prime;
        lower /= prime;
    }

    return result;
}
