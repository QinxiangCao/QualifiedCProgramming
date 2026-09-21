/*@ Extern Coq
      (ModularPower : Z -> Z -> Z -> Z -> Prop)
      (ModularPowerProgress : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib */

int modular_power(int a, int b, int modulus)
/*@ Require
      0 <= a && a < modulus &&
      0 <= b &&
      2 <= modulus && modulus <= 100000 && emp
    Ensure
      ModularPower(a, b, modulus, __return) && emp
 */
{
    int result = 1;

    /*@ Inv Assert
          modulus == modulus@pre &&
          2 <= modulus@pre && modulus@pre <= 100000 &&
          0 <= a && a < modulus@pre &&
          0 <= b &&
          0 <= result && result < modulus@pre &&
          ModularPowerProgress(a@pre, b@pre, modulus@pre,
            a, b, result) && emp
     */
    while (b > 0) {
        if (b % 2 == 1) {
            result = (int)((long long)result * a % modulus);
        }
        a = (int)((long long)a * a % modulus);
        b /= 2;
    }

    return result;
}
