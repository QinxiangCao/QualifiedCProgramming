/*@ Extern Coq
      (ModularMul : Z -> Z -> Z -> Z -> Prop)
      (ModularMulProgress : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib */

int modular_mul(int a, int b, int modulus)
/*@ Require
      0 - modulus < a && a < modulus &&
      INT_MIN < b && b <= INT_MAX &&
      0 < modulus && modulus * 2 <= INT_MAX && emp
    Ensure
      ModularMul(a, b, modulus, __return) && emp
*/
{
    int res = 0;
    int flag = 1;
    if (b < 0) {
        b = -b;
        flag = -1;
    }

    /*@ Inv Assert
          0 - modulus@pre < a@pre && a@pre < modulus@pre &&
          INT_MIN < b@pre && b@pre <= INT_MAX &&
          modulus == modulus@pre &&
          0 < modulus@pre && modulus@pre * 2 <= INT_MAX &&
          0 <= b && b <= INT_MAX &&
          (flag == 1 || flag == 0 - 1) &&
          0 - modulus@pre < a && a < modulus@pre &&
          0 - modulus@pre < res && res < modulus@pre &&
          INT_MIN <= res + a && res + a <= INT_MAX &&
          INT_MIN <= a + a && a + a <= INT_MAX &&
          INT_MIN <= res * flag && res * flag <= INT_MAX &&
          ModularMulProgress(a@pre, b@pre, modulus@pre,
                             a, b, res, flag) && emp
     */
    while (b > 0) {
        if (b % 2 == 1) {
            res = (res + a) % modulus;
        }
        b = b / 2;
        a = (a + a) % modulus;
    }
    return res * flag;
}
