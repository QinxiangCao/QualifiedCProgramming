/*
 * Chinese remainder theorem, using the verified exgcd interface.
 *
 * The moduli are expected to be positive and pairwise coprime.  Under that
 * assumption, the function returns the unique value in [0, product) that is
 * congruent to remainders[i] modulo moduli[i] for every 0 <= i < n.
 *
 * This verification example deliberately uses int throughout.  As requested,
 * choosing inputs whose intermediate products fit in int is left outside the
 * algorithmic presentation here.
 */

/*@ Extern Coq
      (Zgcd: Z -> Z -> Z)
      (CRTProduct: list Z -> Z)
      (CRTInputValid: list Z -> list Z -> Prop)
      (CRTMachineSafe: list Z -> list Z -> Prop)
      (CanonicalCRTSolution: list Z -> list Z -> Z -> Prop)
      (CRTProcessedCongruences: list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib */

int exgcd(int a, int b, int *x, int *y)
/*@ Require
      INT_MIN < a && a <= INT_MAX &&
      INT_MIN < b && b <= INT_MAX &&
      has_int_permission(x) * has_int_permission(y)
    Ensure
      __return == Zgcd(a, b) &&
      a * (*x) + b * (*y) == Zgcd(a, b)
*/;

int chinese_remainder_theorem(int n, int *remainders, int *moduli)
/*@ With (remainders_l moduli_l : list Z)
    Require
      n == Zlength(moduli_l) &&
      CRTInputValid(remainders_l, moduli_l) &&
      CRTMachineSafe(remainders_l, moduli_l) &&
      IntArray::full(remainders, n, remainders_l) *
      IntArray::full(moduli, n, moduli_l)
    Ensure
      CanonicalCRTSolution(remainders_l, moduli_l, __return) &&
      IntArray::full(remainders, n, remainders_l) *
      IntArray::full(moduli, n, moduli_l)
 */
{
    int product = 1;

    /*@ Inv Assert
          n == n@pre &&
          remainders == remainders@pre &&
          moduli == moduli@pre &&
          n@pre == Zlength(moduli_l) &&
          CRTInputValid(remainders_l, moduli_l) &&
          CRTMachineSafe(remainders_l, moduli_l) &&
          0 <= i && i <= n@pre &&
          product == CRTProduct(sublist(0, i, moduli_l)) &&
          1 <= product &&
          product <= CRTProduct(moduli_l) &&
          CRTProduct(moduli_l) <= 46340 &&
          IntArray::full(remainders@pre, n@pre, remainders_l) *
          IntArray::full(moduli@pre, n@pre, moduli_l)
     */
    for (int i = 0; i < n; ++i) {
        product *= moduli[i];
    }

    int result = 0;

    /*@ Inv Assert
          n == n@pre &&
          remainders == remainders@pre &&
          moduli == moduli@pre &&
          n@pre == Zlength(moduli_l) &&
          CRTInputValid(remainders_l, moduli_l) &&
          CRTMachineSafe(remainders_l, moduli_l) &&
          product == CRTProduct(moduli_l) &&
          1 <= product && product <= 46340 &&
          0 <= i && i <= n@pre &&
          0 <= result && result < product &&
          CRTProcessedCongruences(remainders_l, moduli_l, i, result) &&
          (forall (k: Z),
            (i <= k && k < n@pre) =>
            result % Znth(k, moduli_l, 0) == 0) &&
          IntArray::full(remainders@pre, n@pre, remainders_l) *
          IntArray::full(moduli@pre, n@pre, moduli_l)
     */
    for (int i = 0; i < n; ++i) {
        int partial_product = product / moduli[i];
        int coefficient;
        int unused;

        exgcd(partial_product, moduli[i], &coefficient, &unused);

        int term = (coefficient * partial_product) % product;
        term = (term * remainders[i]) % product;
        if (term < 0) {
            term += product;
        }

        result = (result + term) % product;
    }

    return result;
}
