/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq
      (PrefixMaximum : list Z -> Z -> Z -> Prop)
      (DecimalExponent : Z -> Prop)
      (RadixDigit : Z -> Z -> Z)
      (RadixPassState : list Z -> list Z -> Z -> Prop)
      (DigitHistogramPrefix : list Z -> Z -> Z -> list Z -> Prop)
      (DigitPrefixTotals : list Z -> list Z -> Z -> Prop)
      (BucketPlacementProgress : list Z -> Z -> Z -> list Z -> list Z -> list (option Z) -> Prop)
      (StableDigitPass : list Z -> list Z -> Z -> Prop)
      (RadixCopyPrefix : list Z -> list Z -> list Z -> Z -> Prop)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib */

/*
 * Stable decimal-bucket radix sort for non-negative integers.
 * Each pass distributes the input by one decimal digit and writes the
 * buckets back in order.  Processing from right to left keeps a pass stable.
 */
void sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(input) == n &&
      (forall (i : Z),
         (0 <= i && i < n) =>
         (0 <= Znth(i, input, 0) && Znth(i, input, 0) <= 999999999)) &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        Zlength(output) == n &&
        Permutation(input, output) &&
        increasing(output) &&
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
        Zlength(input) == n@pre &&
        1 <= i && i <= n@pre &&
        0 <= max_value && max_value <= 999999999 &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
          (0 <= Znth(k, input, 0) &&
           Znth(k, input, 0) <= 999999999)) &&
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
        Zlength(input) == n@pre &&
        Zlength(current) == n@pre &&
        0 <= max_value && max_value <= 999999999 &&
        1 <= exponent && exponent <= 1000000000 &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
          (0 <= Znth(k, input, 0) &&
           Znth(k, input, 0) <= 999999999)) &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
          (0 <= Znth(k, current, 0) &&
           Znth(k, current, 0) <= 999999999)) &&
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
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(zero_prefix) == digit &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            0 <= digit && digit <= 10 &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < digit) =>
              Znth(k, zero_prefix, 0) == 0) &&
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

        /*@ Assert
            exists current counts,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(counts) == 10 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999)) &&
            (forall (digit : Z),
              (0 <= digit && digit < 10) =>
              Znth(digit, counts, 0) == 0) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            DigitHistogramPrefix(current, exponent, 0, counts) &&
            IntArray::full(a, n@pre, current) *
            IntArray::full(count, 10, counts) *
            IntArray::undef_full(output, 1000)
         */
        /*@ Inv Assert
            exists current counts,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(counts) == 10 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            0 <= i && i <= n@pre &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999)) &&
            (forall (digit : Z),
              (0 <= digit && digit < 10) =>
              (0 <= Znth(digit, counts, 0) &&
               Znth(digit, counts, 0) <= i)) &&
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
            /*@ 0 <= digit && digit < 10 by local */
            ++count[digit];
        }

        /*@ Assert
            exists current histogram,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(histogram) == 10 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999)) &&
            (forall (digit : Z),
              (0 <= digit && digit < 10) =>
              (0 <= Znth(digit, histogram, 0) &&
               Znth(digit, histogram, 0) <= n@pre)) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            DigitHistogramPrefix(current, exponent, n@pre, histogram) &&
            IntArray::full(a, n@pre, current) *
            IntArray::full(count, 10, histogram) *
            IntArray::undef_full(output, 1000)
         */
        /*@ Inv Assert
            exists current histogram totals,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(histogram) == 10 &&
            Zlength(totals) == 10 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            1 <= digit && digit <= 10 &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < 10) =>
              (0 <= Znth(k, histogram, 0) &&
               Znth(k, histogram, 0) <= n@pre)) &&
            (forall (k : Z),
              (0 <= k && k < 10) =>
              (0 <= Znth(k, totals, 0) &&
               Znth(k, totals, 0) <= n@pre)) &&
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

        /*@ Assert
            exists current histogram endpoints,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(histogram) == 10 &&
            Zlength(endpoints) == 10 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999)) &&
            (forall (digit : Z),
              (0 <= digit && digit < 10) =>
              (0 <= Znth(digit, histogram, 0) &&
               Znth(digit, histogram, 0) <= n@pre &&
               0 <= Znth(digit, endpoints, 0) &&
               Znth(digit, endpoints, 0) <= n@pre)) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            DigitHistogramPrefix(current, exponent, n@pre, histogram) &&
            DigitPrefixTotals(histogram, endpoints, 10) &&
            IntArray::full(a, n@pre, current) *
            IntArray::full(count, 10, endpoints) *
            IntArray::undef_full(output, 1000)
         */
        /*@ Inv Assert
            exists current histogram counters mixed_output,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(histogram) == 10 &&
            Zlength(counters) == 10 &&
            Zlength(mixed_output) == 1000 &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            -1 <= i && i < n@pre &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999 &&
               0 <= (Znth(k, current, 0) / exponent) % 10 &&
               (Znth(k, current, 0) / exponent) % 10 < 10)) &&
            (forall (digit : Z),
              (0 <= digit && digit < 10) =>
              (0 <= Znth(digit, histogram, 0) &&
               Znth(digit, histogram, 0) <= n@pre &&
               0 <= Znth(digit, counters, 0) &&
               Znth(digit, counters, 0) <= n@pre)) &&
            (forall (k : Z),
              (0 <= k && k <= i) =>
              (1 <= Znth(
                       (Znth(k, current, 0) / exponent) % 10,
                       counters, 0) &&
               Znth(
                 (Znth(k, current, 0) / exponent) % 10,
                 counters, 0) <= n@pre)) &&
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
            /*@ Given current counters */
            int digit = (a[i] / exponent) % 10;
            /*@ 0 <= digit && digit < 10 &&
                digit == (Znth(i, current, 0) / exponent) % 10 &&
                1 <= Znth(digit, counters, 0) &&
                Znth(digit, counters, 0) <= n@pre by local */
            --count[digit];
            /*@ 0 <= Znth(
                       digit,
                       replace_Znth(
                         digit, Znth(digit, counters, 0) - 1, counters),
                       0) &&
                Znth(
                  digit,
                  replace_Znth(
                    digit, Znth(digit, counters, 0) - 1, counters),
                  0) < 1000 by local */
            output[count[digit]] = a[i];
        }

        /*@ Assert
            exists current histogram bucket_starts pass_output,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(histogram) == 10 &&
            Zlength(bucket_starts) == 10 &&
            Zlength(pass_output) == n@pre &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999 &&
               0 <= Znth(k, pass_output, 0) &&
               Znth(k, pass_output, 0) <= 999999999)) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent) &&
            RadixPassState(input, current, exponent) &&
            DigitHistogramPrefix(current, exponent, n@pre, histogram) &&
            StableDigitPass(current, pass_output, exponent) &&
            IntArray::full(a, n@pre, current) *
            IntArray::full(count, 10, bucket_starts) *
            IntArray::seg(output, 0, n@pre, pass_output) *
            IntArray::undef_seg(output, n@pre, 1000)
         */
        /*@ Inv Assert
            exists current bucket_starts pass_output working,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(current) == n@pre &&
            Zlength(bucket_starts) == 10 &&
            Zlength(pass_output) == n@pre &&
            Zlength(working) == n@pre &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            0 < max_value / exponent &&
            0 <= i && i <= n@pre &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, current, 0) &&
               Znth(k, current, 0) <= 999999999 &&
               0 <= Znth(k, pass_output, 0) &&
               Znth(k, pass_output, 0) <= 999999999 &&
               0 <= Znth(k, working, 0) &&
               Znth(k, working, 0) <= 999999999)) &&
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

        /*@ Assert
            exists pass_output,
            a == a@pre && n == n@pre &&
            2 <= n@pre && n@pre <= 1000 &&
            Zlength(input) == n@pre &&
            Zlength(pass_output) == n@pre &&
            0 <= max_value && max_value <= 999999999 &&
            1 <= exponent && exponent <= 100000000 &&
            1 <= exponent * 10 && exponent * 10 <= 1000000000 &&
            0 < max_value / exponent &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, input, 0) &&
               Znth(k, input, 0) <= 999999999)) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
              (0 <= Znth(k, pass_output, 0) &&
               Znth(k, pass_output, 0) <= 999999999)) &&
            PrefixMaximum(input, n@pre, max_value) &&
            DecimalExponent(exponent * 10) &&
            RadixPassState(input, pass_output, exponent * 10) &&
            IntArray::full(a, n@pre, pass_output) *
            IntArray::undef_full(output, 1000) *
            IntArray::undef_full(count, 10)
         */
    }

    /*@ Assert
        exists final,
        a == a@pre && n == n@pre &&
        2 <= n@pre && n@pre <= 1000 &&
        Zlength(input) == n@pre &&
        Zlength(final) == n@pre &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
          (0 <= Znth(k, input, 0) &&
           Znth(k, input, 0) <= 999999999)) &&
        Permutation(input, final) &&
        increasing(final) &&
        IntArray::full(a, n@pre, final) *
        IntArray::undef_full(output, 1000) *
        IntArray::undef_full(count, 10) *
        has_int_permission(&max_value)
     */
}
