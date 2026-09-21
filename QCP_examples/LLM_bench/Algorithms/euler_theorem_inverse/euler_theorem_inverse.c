/*
 * Compute a modular inverse with Euler's theorem.
 *
 * If a and modulus are coprime, Euler's theorem gives
 *
 *     a ^ phi(modulus) = 1 (mod modulus),
 *
 * so a ^ (phi(modulus) - 1) is an inverse of a modulo modulus.
 * This small example deliberately uses int throughout, following 2.cpp.
 */

/*@ Extern Coq
      (Zgcd : Z -> Z -> Z)
      (EulerPhi : Z -> Z -> Prop)
      (ModularPower : Z -> Z -> Z -> Z -> Prop)
      (EulerTheoremInverse : Z -> Z -> Z -> Prop)
      (EulerPhiProgress : Z -> Z -> Z -> Z -> Prop)
      (EulerPhiRemovalProgress : Z -> Z -> Z -> Z -> Prop)
      (EulerModularPowerProgress : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib */

int euler_phi(int value)
/*@ Require
      2 <= value && value <= 46341 && emp
    Ensure
      1 <= __return && __return <= value &&
      EulerPhi(value, __return) && emp
 */
{
    int result = value;

    /*@ Inv Assert
          2 <= value@pre && value@pre <= 46341 &&
          1 <= value && value <= value@pre &&
          1 <= result && result <= value@pre &&
          2 <= factor && factor <= 216 &&
          EulerPhiProgress(value@pre, factor, value, result) && emp
     */
    for (int factor = 2; factor * factor <= value; ++factor) {
        if (value % factor == 0) {
            /*@ Inv Assert
                  2 <= value@pre && value@pre <= 46341 &&
                  1 <= value && value <= value@pre &&
                  1 <= result && result <= value@pre &&
                  2 <= factor && factor <= 216 &&
                  EulerPhiRemovalProgress(
                    value@pre, factor, value, result) && emp
             */
            while (value % factor == 0) {
                value /= factor;
            }


            result = result / factor * (factor - 1);
        }
    }

    /*@ Assert
          exists frontier,
          2 <= value@pre && value@pre <= 46341 &&
          1 <= value && value <= value@pre &&
          1 <= result && result <= value@pre &&
          2 <= frontier && frontier <= 216 &&
          frontier * frontier > value &&
          (value == 1 ||
            (result % value == 0 &&
             1 <= result / value &&
             0 <= (result / value) * (value - 1) &&
             (result / value) * (value - 1) <= value@pre)) &&
          EulerPhiProgress(value@pre, frontier, value, result) && emp
     */
    if (value != 1) {
        result = result / value * (value - 1);
    }

    return result;
}

int modular_power(int base, int exponent, int modulus)
/*@ Require
      0 <= base && base < modulus &&
      0 <= exponent &&
      2 <= modulus && modulus <= 46341 && emp
    Ensure
      0 <= __return && __return < modulus &&
      ModularPower(base, exponent, modulus, __return) && emp
 */
{
    int result = 1;

    /*@ Inv Assert
          modulus == modulus@pre &&
          2 <= modulus@pre && modulus@pre <= 46341 &&
          0 <= base && base < modulus@pre &&
          0 <= exponent &&
          0 <= result && result < modulus@pre &&
          EulerModularPowerProgress(
            base@pre, exponent@pre, modulus@pre,
            base, exponent, result) && emp
     */
    while (exponent > 0) {
        if (exponent % 2 == 1) {
            result = result * base % modulus;
        }
        base = base * base % modulus;
        exponent /= 2;
    }

    return result;
}

int euler_theorem_inverse(int value, int modulus)
/*@ Require
      0 < value && value < modulus &&
      2 <= modulus && modulus <= 46341 &&
      Zgcd(value, modulus) == 1 && emp
    Ensure
      0 <= __return && __return < modulus &&
      EulerTheoremInverse(value, modulus, __return) && emp
 */
{
    int exponent = euler_phi(modulus) - 1;


    return modular_power(value, exponent, modulus);
}
