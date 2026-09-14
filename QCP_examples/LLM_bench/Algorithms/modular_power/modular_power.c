/*@ Extern Coq
      (ModularPower : Z -> Z -> Z -> Z -> Prop)
      (ModularPowerProgress : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib */

int modular_power(int a, int b, int modulus)
/*@ Require
      0 <= a && a < modulus &&
      0 <= b &&
      2 <= modulus && modulus <= 46341 && emp
    Ensure
      0 <= __return && __return < modulus &&
      ModularPower(a, b, modulus, __return) && emp
 */
{
    int result = 1;

    /*@ Inv Assert
          0 <= a@pre && a@pre < modulus@pre &&
          0 <= b@pre &&
          modulus == modulus@pre &&
          2 <= modulus@pre && modulus@pre <= 46341 &&
          0 <= a && a < modulus@pre &&
          0 <= b && b <= b@pre &&
          0 <= result && result < modulus@pre &&
          0 <= a * a && a * a <= INT_MAX &&
          0 <= result * a && result * a <= INT_MAX &&
          ModularPowerProgress(a@pre, b@pre, modulus@pre,
            a, b, result) && emp
     */
    while (b > 0) {
        if (b % 2 == 1) {
            result = result * a % modulus;
        }
        a = a * a % modulus;
        b /= 2;
    }

    return result;
}
