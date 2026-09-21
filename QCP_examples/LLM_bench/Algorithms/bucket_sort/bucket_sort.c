/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (PrefixMaximum : list Z -> Z -> Z -> Prop)
      (DecimalExponent : Z -> Prop)
      (RadixPassState : list Z -> list Z -> Z -> Prop)
      (DigitHistogramPrefix : list Z -> Z -> Z -> list Z -> Prop)
      (DigitPrefixTotals : list Z -> list Z -> Z -> Prop)
      (BucketPlacementProgress : list Z -> Z -> Z -> list Z -> list Z -> list (option Z) -> Prop)
      (StableDigitPass : list Z -> list Z -> Z -> Prop)
      (RadixCopyPrefix : list Z -> list Z -> list Z -> Z -> Prop)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib */

/* Stable decimal-bucket radix sort for non-negative integers.
 * The result is an increasing permutation of the input. */
void sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= 1000 &&
      Forall(Z::le(0), input) && Forall(Z::ge(999999999), input) &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        Permutation(input, output) && increasing(output) &&
        IntArray::full(a, n, output)
 */
{
    if (n <= 1) {
        return;
    }

    int max_value = a[0];
    /*@ Inv Assert
        a == a@pre && n == n@pre &&
        2 <= n@pre && n@pre <= 1000 &&
        1 <= i && i <= n@pre &&
        0 <= max_value && max_value <= 999999999 &&
        Forall(Z::le(0), input) && Forall(Z::ge(999999999), input) &&
        PrefixMaximum(input, i, max_value) &&
        IntArray::full(a, n@pre, input)
     */
    for (int i = 1; i < n; ++i) {
        if (a[i] > max_value) {
            max_value = a[i];
        }
    }

    int output[1000];
    int count[10];

    /*@ Inv Assert
        exists current,
        a == a@pre && n == n@pre &&
        2 <= n@pre && n@pre <= 1000 &&
        0 <= max_value && max_value <= 999999999 &&
        1 <= exponent && exponent <= 1000000000 &&
        Forall(Z::le(0), current) && Forall(Z::ge(999999999), current) &&
        PrefixMaximum(input, n@pre, max_value) &&
        DecimalExponent(exponent) &&
        RadixPassState(input, current, exponent) &&
        IntArray::full(a, n@pre, current) *
        IntArray::undef_full(output, 1000) *
        IntArray::undef_full(count, 10)
     */
    for (int exponent = 1; max_value / exponent > 0; exponent *= 10) {
        /*@ Inv Assert
            exists current zero_prefix,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            0 <= digit && digit <= 10 &&
            Forall(Z::le(0), current) && Forall(Z::ge(999999999), current) &&
            Forall(eq(0), zero_prefix) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            IntArray::full(a, n@pre, current) *
            IntArray::seg(count, 0, digit, zero_prefix) *
            IntArray::undef_seg(count, digit, 10) *
            IntArray::undef_full(output, 1000)
         */
        for (int digit = 0; digit < 10; ++digit) {
            count[digit] = 0;
        }

        /*@ Inv Assert
            exists current counts,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            0 <= i && i <= n@pre &&
            Forall(Z::le(0), current) && Forall(Z::ge(999999999), current) &&
            Forall(Z::le(0), counts) && Forall(Z::ge(i), counts) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            DigitHistogramPrefix(current, exponent, i, counts) &&
            IntArray::full(a, n@pre, current) *
            IntArray::full(count, 10, counts) *
            IntArray::undef_full(output, 1000)
         */
        for (int i = 0; i < n; ++i) {
            int digit = (a[i] / exponent) % 10;
            /*@ Assert
                exists current counts,
                a == a@pre && n == n@pre &&
                2 <= n@pre && n@pre <= 1000 &&
                0 <= max_value && max_value <= 999999999 &&
                1 <= exponent && exponent <= 100000000 &&
                0 < max_value / exponent &&
                0 <= i && i < n@pre &&
                Forall(Z::le(0), current) && Forall(Z::ge(999999999), current) &&
                Forall(Z::le(0), counts) && Forall(Z::ge(i), counts) &&
                PrefixMaximum(input, n@pre, max_value) &&
                DecimalExponent(exponent) &&
                RadixPassState(input, current, exponent) &&
                DigitHistogramPrefix(current, exponent, i, counts) &&
                digit == (Znth(i, current, 0) / exponent) % 10 &&
                0 <= digit && digit < 10 &&
                IntArray::full(a, n@pre, current) *
                IntArray::full(count, 10, counts) *
                IntArray::undef_full(output, 1000)
             */
            ++count[digit];
        }

        /*@ Inv Assert
            exists current histogram totals,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(histogram) == 10 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            1 <= digit && digit <= 10 &&
            Forall(Z::le(0), current) && Forall(Z::ge(999999999), current) &&
            Forall(Z::le(0), histogram) && Forall(Z::ge(n@pre), histogram) &&
            Forall(Z::le(0), totals) && Forall(Z::ge(n@pre), totals) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            DigitHistogramPrefix(current, exponent, n@pre, histogram) &&
            DigitPrefixTotals(histogram, totals, digit) &&
            IntArray::full(a, n@pre, current) *
            IntArray::full(count, 10, totals) *
            IntArray::undef_full(output, 1000)
         */
        for (int digit = 1; digit < 10; ++digit) {
            count[digit] += count[digit - 1];
        }

        /*@ Inv Assert
            exists current histogram counters mixed_output,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(histogram) == 10 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            -1 <= i && i < n@pre &&
            Forall(Z::le(0), current) && Forall(Z::ge(999999999), current) &&
            Forall(Z::le(0), histogram) && Forall(Z::ge(n@pre), histogram) &&
            Forall(Z::le(0), counters) && Forall(Z::ge(n@pre), counters) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            DigitHistogramPrefix(current, exponent, n@pre, histogram) &&
            BucketPlacementProgress(
              current, exponent, i + 1, histogram, counters, mixed_output) &&
            IntArray::full(a, n@pre, current) *
            IntArray::full(count, 10, counters) *
            IntArray::mixed_full(output, 1000, mixed_output)
         */
        for (int i = n - 1; i >= 0; --i) {
            int digit = (a[i] / exponent) % 10;
            /*@ Assert
                exists current histogram counters mixed_output,
                a == a@pre && n == n@pre &&
                2 <= n@pre && n@pre <= 1000 &&
                Zlength(histogram) == 10 &&
                0 <= max_value && max_value <= 999999999 &&
                1 <= exponent && exponent <= 100000000 &&
                0 < max_value / exponent &&
                0 <= i && i < n@pre &&
                Forall(Z::le(0), current) && Forall(Z::ge(999999999), current) &&
                Forall(Z::le(0), histogram) && Forall(Z::ge(n@pre), histogram) &&
                Forall(Z::le(0), counters) && Forall(Z::ge(n@pre), counters) &&
                PrefixMaximum(input, n@pre, max_value) &&
                DecimalExponent(exponent) &&
                RadixPassState(input, current, exponent) &&
                DigitHistogramPrefix(current, exponent, n@pre, histogram) &&
                BucketPlacementProgress(
                  current, exponent, i + 1, histogram, counters, mixed_output) &&
                digit == (Znth(i, current, 0) / exponent) % 10 &&
                0 <= digit && digit < 10 &&
                1 <= Znth(digit, counters, 0) &&
                Znth(digit, counters, 0) <= n@pre &&
                IntArray::full(a, n@pre, current) *
                store(pointer_offset(count, digit, sizeof(int), int), int, Znth(digit, counters, 0)) *
                IntArray::missing_i(count, digit, 0, 10, counters) *
                IntArray::mixed_full(output, 1000, mixed_output)
             */
            --count[digit];
            output[count[digit]] = a[i];
        }

        /*@ Inv Assert
            exists current bucket_starts pass_output working,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(current) == n@pre &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 <= i && i <= n@pre &&
            Forall(Z::le(0), pass_output) && Forall(Z::ge(999999999), pass_output) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            StableDigitPass(current, pass_output, exponent) &&
            RadixCopyPrefix(current, pass_output, working, i) &&
            IntArray::full(a, n@pre, working) *
            IntArray::full(count, 10, bucket_starts) *
            IntArray::seg(output, 0, n@pre, pass_output) *
            IntArray::undef_seg(output, n@pre, 1000)
         */
        for (int i = 0; i < n; ++i) {
            a[i] = output[i];
        }
    }
}
