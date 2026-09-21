/*
 * Chinese remainder theorem, using the verified exgcd interface.
 *
 * The moduli are expected to be positive and pairwise coprime.  Under that
 * assumption, the function returns the unique value in [0, product) that is
 * congruent to remainders[i] modulo moduli[i] for every 0 <= i < n.
 *
 * The product is at most 46340.  Only the unreduced Bezout multiplication
 * uses long long; all reduced residue operations fit in int.
 */

/*@ Extern Coq
      (Zgcd: Z -> Z -> Z)
      (CRTProduct: list Z -> Z)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::lt : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::div : Z -> Z -> Z)
      (Z::mul : Z -> Z -> Z)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (CRTUnprocessedZero : list Z -> Z -> Z -> Prop)
      (CanonicalCRTSolution: list Z -> list Z -> Z -> Prop)
      (CRTConsistentPrefix: list Z -> list Z -> Z -> Z -> Prop)
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
      Zlength(remainders_l) == Zlength(moduli_l) &&
      1 <= Zlength(moduli_l) &&
      Forall(Z::le(1), moduli_l) &&
      Forall(Z::le(0), remainders_l) &&
      Forall2(Z::lt, remainders_l, moduli_l) &&
      (forall (j k: Z),
        (0 <= j && j < k && k < Zlength(moduli_l)) =>
        Zgcd(Znth(j, moduli_l, 0), Znth(k, moduli_l, 0)) == 1) &&
      1 <= CRTProduct(moduli_l) && CRTProduct(moduli_l) <= 46340 &&
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
          Zlength(remainders_l) == Zlength(moduli_l) &&
          1 <= Zlength(moduli_l) &&
          Forall(Z::le(1), moduli_l) &&
          Forall(Z::le(0), remainders_l) &&
          Forall2(Z::lt, remainders_l, moduli_l) &&
          (forall (j k: Z),
            (0 <= j && j < k && k < Zlength(moduli_l)) =>
            Zgcd(Znth(j, moduli_l, 0), Znth(k, moduli_l, 0)) == 1) &&
          1 <= CRTProduct(moduli_l) && CRTProduct(moduli_l) <= 46340 &&
          0 <= i && i <= n@pre &&
          product == CRTProduct(sublist(0, i, moduli_l)) &&
          1 <= product &&
          product <= CRTProduct(moduli_l) &&
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
          Zlength(remainders_l) == Zlength(moduli_l) &&
          1 <= Zlength(moduli_l) &&
          Forall(Z::le(1), moduli_l) &&
          Forall(Z::le(0), remainders_l) &&
          Forall2(Z::lt, remainders_l, moduli_l) &&
          (forall (j k: Z),
            (0 <= j && j < k && k < Zlength(moduli_l)) =>
            Zgcd(Znth(j, moduli_l, 0), Znth(k, moduli_l, 0)) == 1) &&
          1 <= CRTProduct(moduli_l) && CRTProduct(moduli_l) <= 46340 &&
          product == CRTProduct(moduli_l) &&
          1 <= product && product <= 46340 &&
          0 <= i && i <= n@pre &&
          0 <= result && result < product &&
          CRTConsistentPrefix(remainders_l, moduli_l, i, result) &&
          CRTUnprocessedZero(moduli_l, i, result) &&
          IntArray::full(remainders@pre, n@pre, remainders_l) *
          IntArray::full(moduli@pre, n@pre, moduli_l)
     */
    for (int i = 0; i < n; ++i) {
        int partial_product = product / moduli[i];
        int coefficient;
        int unused;

        exgcd(partial_product, moduli[i], &coefficient, &unused);

        /* The Bezout coefficient may be any int.  Widen before multiplying;
           reduce modulo product before converting the result back to int. */
        int term = (int)(((long long)coefficient * partial_product) % product);
        term = (term * remainders[i]) % product;
        if (term < 0) {
            term += product;
        }

        result = (result + term) % product;
    }

    return result;
}
