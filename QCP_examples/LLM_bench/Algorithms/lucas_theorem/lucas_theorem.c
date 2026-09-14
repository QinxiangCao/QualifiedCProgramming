/*
 * Compute C(n + m, n) modulo a prime p with Lucas' theorem.
 *
 * The problem guarantees
 *
 *   1 <= n, m, p <= 100000
 *
 * and that p is prime.  For this verification example, all arithmetic used by
 * the program is additionally assumed to stay within the signed int range.
 *
 * Input/output handling is intentionally left to the caller.  The function
 * lucas_theorem is the algorithmic entry point for one test case.
 */

/*@ Extern Coq
      (ModularPower : Z -> Z -> Z -> Z -> Prop)
 */
/*@ Extern Coq
      (PrimeForLucas : Z -> Prop)
      (DigitBinomialMachineSafe : Z -> Z -> Z -> Prop)
      (BinomialDigitResidue : Z -> Z -> Z -> Z -> Prop)
      (LucasMachineSafe : Z -> Z -> Z -> Prop)
      (LucasBinomialResidue : Z -> Z -> Z -> Z -> Prop)
 */
/*@ Extern Coq
      (DigitProductProgress : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (LucasProgress : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_lib */

int modular_power(int base, int exponent, int modulus)
/*@ Require
      0 <= base && base < modulus &&
      0 <= exponent && 2 <= modulus && emp
    Ensure
      0 <= __return && __return < modulus &&
      ModularPower(base, exponent, modulus, __return) && emp
 */;

/*
 * Compute C(upper, lower) modulo prime, where
 * 0 <= lower <= upper < prime.
 *
 * Because every factor in lower! is nonzero modulo prime, Fermat's little
 * theorem gives lower!^(prime - 2) as its modular inverse.
 */
int binomial_digit_mod_prime(int upper, int lower, int prime)
/*@ Require
      PrimeForLucas(prime) &&
      0 <= lower && lower <= upper && upper < prime &&
      2 <= prime && prime <= 100000 &&
      DigitBinomialMachineSafe(upper, lower, prime) && emp
    Ensure
      0 <= __return && __return < prime@pre &&
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
          PrimeForLucas(prime@pre) &&
          0 <= lower@pre && lower@pre <= upper@pre &&
          upper@pre < prime@pre &&
          2 <= prime@pre && prime@pre <= 100000 &&
          ((lower == lower@pre &&
            lower@pre <= upper@pre - lower@pre) ||
           (lower == upper@pre - lower@pre &&
            lower@pre > upper@pre - lower@pre)) &&
          0 <= lower && lower <= upper@pre - lower &&
          1 <= i && i <= lower + 1 &&
          0 <= numerator && numerator < prime@pre &&
          0 <= denominator && denominator < prime@pre &&
          DigitBinomialMachineSafe(upper@pre, lower@pre, prime@pre) &&
          DigitProductProgress(upper@pre, lower, prime@pre,
            i, numerator, denominator) && emp
     */
    for (int i = 1; i <= lower; ++i) {
        int factor = upper - lower + i;
        int numerator_product = numerator * factor;
        int denominator_product = denominator * i;

        numerator = numerator_product % prime;
        denominator = denominator_product % prime;
    }

    /*@ Assert
          upper == upper@pre && prime == prime@pre &&
          PrimeForLucas(prime@pre) &&
          0 <= lower@pre && lower@pre <= upper@pre &&
          upper@pre < prime@pre &&
          2 <= prime@pre && prime@pre <= 100000 &&
          ((lower == lower@pre &&
            lower@pre <= upper@pre - lower@pre) ||
           (lower == upper@pre - lower@pre &&
            lower@pre > upper@pre - lower@pre)) &&
          0 <= lower && lower <= upper@pre - lower &&
          0 <= numerator && numerator < prime@pre &&
          0 <= denominator && denominator < prime@pre &&
          0 <= prime@pre - 2 &&
          DigitBinomialMachineSafe(upper@pre, lower@pre, prime@pre) &&
          DigitProductProgress(upper@pre, lower, prime@pre,
            lower + 1, numerator, denominator) && emp
     */
    int inverse = modular_power(denominator, prime - 2, prime);
    int answer = numerator * inverse;
    return answer % prime;
}

int lucas_theorem(int n, int m, int prime)
/*@ Require
      1 <= n && n <= 100000 &&
      1 <= m && m <= 100000 &&
      2 <= prime && prime <= 100000 &&
      PrimeForLucas(prime) &&
      LucasMachineSafe(n, m, prime) && emp
    Ensure
      0 <= __return && __return < prime@pre &&
      LucasBinomialResidue(n@pre, m@pre, prime@pre, __return) && emp
 */
{
    int upper = n + m;
    int lower = n;
    int result = 1;

    /*@ Inv Assert
          n == n@pre && m == m@pre && prime == prime@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          2 <= prime@pre && prime@pre <= 100000 &&
          PrimeForLucas(prime@pre) &&
          LucasMachineSafe(n@pre, m@pre, prime@pre) &&
          0 <= lower && lower <= upper &&
          upper <= n@pre + m@pre && n@pre + m@pre <= 200000 &&
          0 <= result && result < prime@pre &&
          LucasProgress(n@pre + m@pre, n@pre, prime@pre,
            upper, lower, result) && emp
     */
    while (upper > 0 || lower > 0) {
        int upper_digit = upper % prime;
        int lower_digit = lower % prime;

        if (lower_digit > upper_digit) {
            return 0;
        }

        /*@ Assert
              n == n@pre && m == m@pre && prime == prime@pre &&
              1 <= n@pre && n@pre <= 100000 &&
              1 <= m@pre && m@pre <= 100000 &&
              2 <= prime@pre && prime@pre <= 100000 &&
              PrimeForLucas(prime@pre) &&
              LucasMachineSafe(n@pre, m@pre, prime@pre) &&
              0 < upper && 0 <= lower && lower <= upper &&
              upper <= n@pre + m@pre && n@pre + m@pre <= 200000 &&
              upper_digit == upper % prime@pre &&
              lower_digit == lower % prime@pre &&
              0 <= lower_digit && lower_digit <= upper_digit &&
              upper_digit < prime@pre &&
              0 <= result && result < prime@pre &&
              DigitBinomialMachineSafe(
                upper_digit, lower_digit, prime@pre) &&
              LucasProgress(n@pre + m@pre, n@pre, prime@pre,
                upper, lower, result) && emp
         */
        int digit_binomial =
            binomial_digit_mod_prime(upper_digit, lower_digit, prime);
        int product = result * digit_binomial;
        result = product % prime;

        upper /= prime;
        lower /= prime;
    }

    return result;
}
