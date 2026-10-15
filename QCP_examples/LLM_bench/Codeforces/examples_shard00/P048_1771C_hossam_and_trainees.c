/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
*/

/* Codeforces 1771/C - Hossam and Trainees */
// #include <stdio.h>
// #include <stdlib.h>

static int cmp_int(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}

/* QCP_INSERT_BEGIN:P048_1771C_hossam_and_trainees.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib */
/* QCP_INSERT_END:P048_1771C_hossam_and_trainees.support */

/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (PrimePrefixTable : Z -> list Z -> list Z -> Prop)
      (PrimeMarkTable : Z -> Z -> list Z -> list Z -> Prop)
      (CompletePrimeTable : list Z -> Prop)
      (PrimeFactorBagPrefix : list Z -> Z -> list Z -> Prop)
      (FactorScanState : list Z -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (FactorDivideState : list Z -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (DuplicatePrefixState : list Z -> Z -> Z -> Prop)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::full_shape : Z -> Z -> Assertion)
      (UCharArray::full : Z -> Z -> list Z -> Assertion)
      (UCharArray::undef_full : Z -> Z -> Assertion)
      (UCharArray::full_shape : Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (PrimePrefixTable2 : Z -> list Z -> list Z -> Prop)
      (PrimeMarkTable2 : Z -> Z -> list Z -> list Z -> Prop)
      (FactorAppendCapacity : list Z -> Z -> Z -> Z -> Z -> Prop)
      (DuplicateScanLoopState : list Z -> Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (FactorScanState2 : list Z -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (FactorDivideState2 : list Z -> list Z -> Z -> Z -> Z -> list Z -> Prop)
*/

void *malloc(unsigned int size)
    /*@ malloc_int
  With (cap : Z)
  Require
    0 <= cap &&
    cap * sizeof(int) <= 4294967295 &&
    size == cap * sizeof(int)
  Ensure
    __return != 0 &&
    IntArray::undef_full(__return, cap)
*/
    ;

void qsort(int *base, unsigned int nmemb, unsigned int size,
           int (*compar)(const void *, const void *))
    /*@ With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      size == sizeof(int) &&
      IntArray::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        increasing(sorted) &&
        Zlength(sorted) == nmemb &&
        IntArray::full(base, nmemb, sorted)
*/
    ;

void free(void *ptr)
    /*@ free_int
  With (len : Z) (cap : Z)
  Require
    0 <= len && len <= cap &&
    exists xs,
      Zlength(xs) == len &&
      IntArray::full(ptr, len, xs) *
      IntArray::undef_seg(ptr, len, cap)
  Ensure emp
*/
    ;

static int solver(const int *values,
                  int n) /* QCP_INSERT_BEGIN:P048_1771C_hossam_and_trainees.contract */

/*@ With (a : list Z)
    Require
      2 <= Zlength(a) && Zlength(a) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(a)) => (1 <= a[i] && a[i] <= 1000000000)) &&
      n == Zlength(a) && IntArray::full(values, n, a)
    Ensure
      Spec(a, __return) &&
      IntArray::full(values, n, a)
*/
/* QCP_INSERT_END:P048_1771C_hossam_and_trainees.contract */

{
    int primes[4000];
    int pc = 0;
    unsigned char composite[31624] = {0};
    /*@ Inv Assert
          exists prime_data composite_data,
            values == values@pre && n == n@pre &&
            n@pre == Zlength(a) &&
            2 <= Zlength(a) && Zlength(a) <= 100000 &&
            (forall k, (0 <= k && k < Zlength(a)) =>
              (1 <= a[k] && a[k] <= 1000000000)) &&
            2 <= i && i <= 31624 &&
            pc == Zlength(prime_data) && 0 <= pc && pc < 4000 &&
            Zlength(composite_data) == 31624 &&
            PrimePrefixTable2(i, prime_data, composite_data) &&
            IntArray::full(values@pre, n@pre, a) *
            IntArray::full(primes, pc, prime_data) *
            IntArray::undef_seg(primes, pc, 4000) *
            UCharArray::full(composite, 31624, composite_data)
    */
    for (int i = 2; i <= 31623; ++i)
        if (!composite[i])
        {
            primes[pc] = i;
            pc++;
            if ((long long)i * i <= 31623)
                /*@ Inv Assert
                      exists prime_data composite_data,
                        values == values@pre && n == n@pre &&
                        n@pre == Zlength(a) &&
                        2 <= Zlength(a) && Zlength(a) <= 100000 &&
                        (forall k, (0 <= k && k < Zlength(a)) =>
                          (1 <= a[k] && a[k] <= 1000000000)) &&
                        2 <= i && i <= 177 &&
                        pc == Zlength(prime_data) && 1 <= pc && pc < 4000 &&
                        i * i <= j && j <= 31623 + i &&
                        Zlength(composite_data) == 31624 &&
                        PrimeMarkTable2(i, j, prime_data, composite_data) &&
                        IntArray::full(values@pre, n@pre, a) *
                        IntArray::full(primes, pc, prime_data) *
                        IntArray::undef_seg(primes, pc, 4000) *
                        UCharArray::full(composite, 31624, composite_data)
                */
                for (int j = i * i; j <= 31623; j += i)
                    composite[j] = 1;
        }
    int *factors = malloc(n * 10 * sizeof(*factors))
        /*@ where (malloc_int) cap = n * 10 */;
    int count = 0;
    /*@ Inv Assert
          exists prime_data composite_data factor_data,
            values == values@pre && n == n@pre &&
            n@pre == Zlength(a) &&
            2 <= Zlength(a) && Zlength(a) <= 100000 &&
            (forall k, (0 <= k && k < Zlength(a)) =>
              (1 <= a[k] && a[k] <= 1000000000)) &&
            0 <= i && i <= n &&
            pc == Zlength(prime_data) && 0 <= pc && pc < 4000 &&
            Zlength(composite_data) == 31624 &&
            count == Zlength(factor_data) &&
            0 <= count && count <= i * 10 &&
            CompletePrimeTable(prime_data) &&
            PrimeFactorBagPrefix(a, i, factor_data) &&
            IntArray::full(values@pre, n@pre, a) *
            IntArray::full(primes, pc, prime_data) *
            IntArray::undef_seg(primes, pc, 4000) *
            UCharArray::full(composite, 31624, composite_data) *
            IntArray::full(factors, count, factor_data) *
            IntArray::undef_seg(factors, count, n * 10)
    */
    for (int i = 0; i < n; ++i)
    {
        int x = values[i];
        /*@ Inv Assert
              exists prime_data composite_data factor_data,
                values == values@pre && n == n@pre &&
                n@pre == Zlength(a) &&
                2 <= Zlength(a) && Zlength(a) <= 100000 &&
                (forall k, (0 <= k && k < Zlength(a)) =>
                  (1 <= a[k] && a[k] <= 1000000000)) &&
                0 <= i && i < n &&
                0 <= j && j <= pc &&
                1 <= x && x <= 1000000000 &&
                pc == Zlength(prime_data) && 0 <= pc && pc < 4000 &&
                Zlength(composite_data) == 31624 &&
                count == Zlength(factor_data) &&
                0 <= count && count <= i * 10 + 9 &&
                CompletePrimeTable(prime_data) &&
                FactorScanState(a, prime_data, i, j, x, factor_data) &&
                FactorScanState2(a, prime_data, i, j, x, factor_data) &&
                FactorAppendCapacity(prime_data, i, j, x, count) &&
                IntArray::full(values@pre, n@pre, a) *
                IntArray::full(primes, pc, prime_data) *
                IntArray::undef_seg(primes, pc, 4000) *
                UCharArray::full(composite, 31624, composite_data) *
                IntArray::full(factors, count, factor_data) *
                IntArray::undef_seg(factors, count, n * 10)
        */
        for (int j = 0; j < pc && (long long)primes[j] * primes[j] <= x; ++j)
            if (x % primes[j] == 0)
            {
                factors[count] = primes[j];
                count++;
                /*@ Inv Assert
                  exists prime_data composite_data factor_data,
                    values == values@pre && n == n@pre &&
                    n@pre == Zlength(a) &&
                    2 <= Zlength(a) && Zlength(a) <= 100000 &&
                    (forall k, (0 <= k && k < Zlength(a)) =>
                      (1 <= a[k] && a[k] <= 1000000000)) &&
                    0 <= i && i < n &&
                    0 <= j && j < pc &&
                    1 <= x && x <= 1000000000 &&
                    pc == Zlength(prime_data) && 0 <= pc && pc < 4000 &&
                    Zlength(composite_data) == 31624 &&
                    count == Zlength(factor_data) &&
                    1 <= count && count <= i * 10 + 9 &&
                    CompletePrimeTable(prime_data) &&
                    FactorDivideState(a, prime_data, i, j, x, factor_data) &&
                    FactorDivideState2(a, prime_data, i, j, x, factor_data) &&
                    IntArray::full(values@pre, n@pre, a) *
                    IntArray::full(primes, pc, prime_data) *
                    IntArray::undef_seg(primes, pc, 4000) *
                    UCharArray::full(composite, 31624, composite_data) *
                    IntArray::full(factors, count, factor_data) *
                    IntArray::undef_seg(factors, count, n * 10)
            */
                while (x % primes[j] == 0)
                    x /= primes[j];
            }
        if (x > 1)
        {
            factors[count] = x;
            count++;
        }
    }
    qsort(factors, count, sizeof(*factors), cmp_int);
    int ok = 0;
    /*@ Inv Assert
          exists prime_data composite_data sorted,
            values == values@pre && n == n@pre &&
            n@pre == Zlength(a) &&
            2 <= Zlength(a) && Zlength(a) <= 100000 &&
            0 <= count && count <= n * 10 &&
            1 <= i && i <= count + 1 &&
            pc == Zlength(prime_data) && 0 <= pc && pc < 4000 &&
            Zlength(composite_data) == 31624 &&
            Zlength(sorted) == count &&
            increasing(sorted) &&
            PrimeFactorBagPrefix(a, n, sorted) &&
            DuplicateScanLoopState(sorted, count, i, ok) &&
            IntArray::full(values@pre, n@pre, a) *
            IntArray::full(primes, pc, prime_data) *
            IntArray::undef_seg(primes, pc, 4000) *
            UCharArray::full(composite, 31624, composite_data) *
            IntArray::full(factors, count, sorted) *
            IntArray::undef_seg(factors, count, n * 10)
    */
    for (int i = 1; i < count; ++i)
        if (factors[i] == factors[i - 1])
            ok = 1;
    /*@ Assert
          exists prime_data composite_data sorted,
            values == values@pre && n == n@pre &&
            n@pre == Zlength(a) &&
            2 <= Zlength(a) && Zlength(a) <= 100000 &&
            0 <= count && count <= n * 10 &&
            pc == Zlength(prime_data) && 0 <= pc && pc < 4000 &&
            Zlength(composite_data) == 31624 &&
            Zlength(sorted) == count &&
            increasing(sorted) &&
            PrimeFactorBagPrefix(a, n, sorted) &&
            DuplicatePrefixState(sorted, count, ok) &&
            Spec(a, ok) &&
            IntArray::full(values@pre, n@pre, a) *
            IntArray::full(primes, pc, prime_data) *
            IntArray::undef_seg(primes, pc, 4000) *
            UCharArray::full(composite, 31624, composite_data) *
            IntArray::full(factors, count, sorted) *
            IntArray::undef_seg(factors, count, n * 10)
    */
    free(factors) /*@ where (free_int) len = count, cap = n * 10 */;
    /*@ Assert
          exists count_value pc_value factor_pointer,
            values == values@pre && n == n@pre &&
            count == count_value && pc == pc_value &&
            factors == factor_pointer &&
            Spec(a, ok) &&
            IntArray::full(values@pre, n@pre, a) *
            IntArray::undef_full(primes, 4000) *
            UCharArray::undef_full(composite, 31624)
    */
    return ok;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); int *values = malloc((size_t)n * sizeof(*values));
//         for (int i = 0; i < n; ++i) scanf("%d", &values[i]);
//         puts(solver(values, n) ? "YES" : "NO"); free(values);
//     }
//     return 0;
// }
