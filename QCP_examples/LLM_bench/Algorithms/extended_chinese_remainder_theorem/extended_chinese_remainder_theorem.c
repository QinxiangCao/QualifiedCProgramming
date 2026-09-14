/*@ Extern Coq
      (Zgcd : Z -> Z -> Z)
      (Zabs : Z -> Z)
      (ModularMul : Z -> Z -> Z -> Z -> Prop)
      (ExtendedCRTInputs : list Z -> list Z -> Z -> Prop)
      (ExtendedCRTSystemCompatible : list Z -> list Z -> Z -> Prop)
      (ExtendedCRTIntSafe : list Z -> Z -> Prop)
      (ExtendedCRTSystemResult : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (CRTPrefixMeaning : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (CRTReducedMergeEquation : Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib */

/*
 * Interface supplied by the verified extended Euclidean algorithm case.
 * This case uses only its contract; the exgcd implementation is verified
 * separately and is intentionally not repeated here.
 */
int exgcd(int a, int b, int *x, int *y)
/*@ Require
      0 < a && a <= INT_MAX &&
      0 < b && b <= INT_MAX &&
      has_int_permission(x) * has_int_permission(y)
    Ensure
      0 < __return &&
      __return == Zgcd(a, b) &&
      a * (*x) + b * (*y) == __return &&
      Zabs(*x) <= b / __return &&
      ((a % b == 0 && *x == 0) || a % b != 0)
*/;

/*
 * Interface supplied by the separately verified modular-multiplication case.
 * This case uses only its contract and intentionally does not repeat its body.
 */
int modular_mul(int a, int b, int modulus)
/*@ Require
      0 - modulus < a && a < modulus &&
      INT_MIN < b && b <= INT_MAX &&
      0 < modulus && modulus * 2 <= INT_MAX && emp
    Ensure
      ModularMul(a, b, modulus, __return) && emp
*/;

/*
 * Solve a compatible system of congruences with the extended Chinese
 * remainder theorem:
 *
 *     answer = residues[i] (mod moduli[i]),  0 <= i < n.
 *
 * The returned answer is the least nonnegative common residue and
 * *combined_modulus is the least common multiple of all input moduli.
 *
 * This implementation intentionally mirrors 3.cpp: start from the first
 * congruence, then use exgcd and modular_mul to merge every remaining
 * congruence into the current answer/lcm pair.  It deliberately uses int
 * throughout; the long-long and data-range-engineering variants are out of
 * scope.
 */
int extended_chinese_remainder_theorem(int n,
                                      int *residues,
                                      int *moduli,
                                      int *combined_modulus)
/*@ With (residue_values modulus_values : list Z)
    Require
      ExtendedCRTInputs(residue_values, modulus_values, n) &&
      ExtendedCRTSystemCompatible(residue_values, modulus_values, n) &&
      ExtendedCRTIntSafe(modulus_values, n) &&
      IntArray::full(residues, n, residue_values) *
      IntArray::full(moduli, n, modulus_values) *
      has_int_permission(combined_modulus)
    Ensure
      ExtendedCRTSystemResult(residue_values, modulus_values, n,
                              __return, *combined_modulus) &&
      IntArray::full(residues, n, residue_values) *
      IntArray::full(moduli, n, modulus_values)
*/
{
    /*@ 1 <= n */
    int answer = residues[0];
    int lcm = moduli[0];

    /*@ Inv Assert
          n == n@pre && residues == residues@pre &&
          moduli == moduli@pre &&
          combined_modulus == combined_modulus@pre &&
          ExtendedCRTInputs(residue_values, modulus_values, n@pre) &&
          ExtendedCRTSystemCompatible(residue_values, modulus_values, n@pre) &&
          ExtendedCRTIntSafe(modulus_values, n@pre) &&
          1 <= i && i <= n@pre &&
          0 <= answer && answer < lcm &&
          0 < lcm && lcm <= INT_MAX &&
          CRTPrefixMeaning(residue_values, modulus_values, i, answer, lcm) &&
          IntArray::full(residues@pre, n@pre, residue_values) *
          IntArray::full(moduli@pre, n@pre, modulus_values) *
          has_int_permission(combined_modulus@pre)
    */
    for (int i = 1; i < n; ++i) {
        int x;
        int y;
        int gcd = exgcd(lcm, moduli[i], &x, &y);
        int reduced_modulus = moduli[i] / gcd;

        /*@ Assert
              n == n@pre && residues == residues@pre &&
              moduli == moduli@pre &&
              combined_modulus == combined_modulus@pre &&
              ExtendedCRTInputs(residue_values, modulus_values, n@pre) &&
              ExtendedCRTSystemCompatible(residue_values, modulus_values,
                                          n@pre) &&
              ExtendedCRTIntSafe(modulus_values, n@pre) &&
              0 <= i && 1 <= i && i < n@pre &&
              0 <= answer && answer < lcm &&
              0 < lcm && lcm <= INT_MAX &&
              CRTPrefixMeaning(residue_values, modulus_values,
                               i, answer, lcm) &&
              gcd == Zgcd(lcm, Znth(i, modulus_values, 0)) &&
              0 < gcd &&
              lcm * x + Znth(i, modulus_values, 0) * y == gcd &&
              reduced_modulus == Znth(i, modulus_values, 0) / gcd &&
              0 < reduced_modulus &&
              reduced_modulus * 2 <= INT_MAX &&
              0 - reduced_modulus < x && x < reduced_modulus &&
              INT_MIN < (Znth(i, residue_values, 0) - answer) / gcd &&
              (Znth(i, residue_values, 0) - answer) / gcd <= INT_MAX &&
              data_at(residues@pre + i * sizeof(int), int,
                      Znth(i, residue_values, 0)) *
              IntArray::missing_i(residues@pre, i, 0, n@pre,
                                  residue_values) *
              IntArray::full(moduli, n@pre, modulus_values) *
              has_int_permission(combined_modulus@pre)
        */

        x = modular_mul(x, (residues[i] - answer) / gcd, reduced_modulus);
        if (x < 0) {
            x += reduced_modulus;
        }

        /*@ Assert
              n == n@pre && residues == residues@pre &&
              moduli == moduli@pre &&
              combined_modulus == combined_modulus@pre &&
              ExtendedCRTInputs(residue_values, modulus_values, n@pre) &&
              ExtendedCRTSystemCompatible(residue_values, modulus_values,
                                          n@pre) &&
              ExtendedCRTIntSafe(modulus_values, n@pre) &&
              1 <= i && i < n@pre &&
              0 <= answer && answer < lcm &&
              0 < lcm && lcm <= INT_MAX &&
              CRTPrefixMeaning(residue_values, modulus_values,
                               i, answer, lcm) &&
              gcd == Zgcd(lcm, Znth(i, modulus_values, 0)) &&
              0 < gcd &&
              reduced_modulus == Znth(i, modulus_values, 0) / gcd &&
              0 < reduced_modulus && reduced_modulus <= INT_MAX &&
              0 <= x && x < reduced_modulus &&
              0 < lcm * reduced_modulus &&
              lcm * reduced_modulus <= INT_MAX &&
              CRTReducedMergeEquation(answer, lcm,
                                      Znth(i, residue_values, 0),
                                      Znth(i, modulus_values, 0), x) &&
              IntArray::full(residues@pre, n@pre, residue_values) *
              IntArray::full(moduli@pre, n@pre, modulus_values) *
              has_int_permission(combined_modulus@pre) *
              has_int_permission(&y)
        */

        answer = answer + x * lcm;
        lcm = lcm * reduced_modulus;
    }

    *combined_modulus = lcm;
    return answer;
}
