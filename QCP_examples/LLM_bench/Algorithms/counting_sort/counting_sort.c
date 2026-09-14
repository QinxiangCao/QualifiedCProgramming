/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (CountingZeroedPrefix : list (option Z) -> Z -> Prop)
      (CountingHistogramPrefix : list Z -> list Z -> Z -> Prop)
      (CountingCumulativeState : list Z -> list Z -> Z -> Prop)
      (CountingSorted : list Z -> list Z -> Prop)
      (CountingPlacementProgress : list Z -> list Z -> list Z -> list (option Z) -> list Z -> Z -> Prop)
      (CountingCopyProgress : list Z -> list Z -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_lib */

/*
 * Stable counting sort for values in the fixed range [0, 99].
 * The cumulative histogram gives the end of each value's bucket; walking the
 * input from right to left makes the placement phase stable.
 */
void sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= 100 &&
      Zlength(input) == n &&
      (forall (i : Z),
         (0 <= i && i < n) =>
         (0 <= Znth(i, input, 0) && Znth(i, input, 0) < 100)) &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        Zlength(output) == n &&
        Permutation(input, output) &&
        increasing(output) &&
        IntArray::full(a, n, output)
 */
{
    int count[100];
    int output[100];

    /*@ Inv Assert
        exists output_mixed count_mixed,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(output_mixed) == 100 &&
          Zlength(count_mixed) == 100 &&
          0 <= value && value <= 100 &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= input[k] && input[k] < 100)) &&
          (forall (k : Z),
            (0 <= k && k < 100) => output_mixed[k] == None) &&
          CountingZeroedPrefix(count_mixed, value) &&
          IntArray::full(a, n@pre, input) *
          IntArray::mixed_full(output, 100, output_mixed) *
          IntArray::mixed_full(count, 100, count_mixed)
    */
    for (int value = 0; value < 100; ++value) {
        count[value] = 0;
    }

    /*@ Assert
        exists output_mixed zeros,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(output_mixed) == 100 &&
          Zlength(zeros) == 100 &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= input[k] && input[k] < 100)) &&
          (forall (k : Z),
            (0 <= k && k < 100) => output_mixed[k] == None) &&
          (forall (value : Z),
            (0 <= value && value < 100) => zeros[value] == 0) &&
          CountingHistogramPrefix(input, zeros, 0) &&
          IntArray::full(a, n@pre, input) *
          IntArray::mixed_full(output, 100, output_mixed) *
          IntArray::full(count, 100, zeros)
    */
    /*@ Inv Assert
        exists output_mixed counts,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(output_mixed) == 100 &&
          Zlength(counts) == 100 &&
          0 <= i && i <= n@pre &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= input[k] && input[k] < 100)) &&
          (forall (value : Z),
            (0 <= value && value < 100) =>
            (0 <= counts[value] && counts[value] <= i)) &&
          (forall (k : Z),
            (0 <= k && k < 100) => output_mixed[k] == None) &&
          CountingHistogramPrefix(input, counts, i) &&
          IntArray::full(a, n@pre, input) *
          IntArray::mixed_full(output, 100, output_mixed) *
          IntArray::full(count, 100, counts)
    */
    for (int i = 0; i < n; ++i) {
        /*@ Given counts */
        /*@ 0 <= input[i] && input[i] < 100 &&
            0 <= counts[input[i]] && counts[input[i]] < 100 by local */
        ++count[a[i]];
    }

    /*@ Inv Assert
        exists output_mixed positions,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(output_mixed) == 100 &&
          Zlength(positions) == 100 &&
          1 <= value && value <= 100 &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= input[k] && input[k] < 100)) &&
          (forall (bucket : Z),
            (0 <= bucket && bucket < 100) =>
            (0 <= positions[bucket] && positions[bucket] <= n@pre)) &&
          (value < 100 =>
            positions[value] + positions[value - 1] <= n@pre) &&
          (forall (k : Z),
            (0 <= k && k < 100) => output_mixed[k] == None) &&
          CountingCumulativeState(input, positions, value) &&
          IntArray::full(a, n@pre, input) *
          IntArray::mixed_full(output, 100, output_mixed) *
          IntArray::full(count, 100, positions)
    */
    for (int value = 1; value < 100; ++value) {
        count[value] += count[value - 1];
    }

    /*@ Inv Assert
        exists positions bucket_ends output_mixed sorted,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(sorted) == n@pre &&
          Zlength(positions) == 100 &&
          Zlength(bucket_ends) == 100 &&
          Zlength(output_mixed) == 100 &&
          -1 <= i && i < n@pre &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= input[k] && input[k] < 100)) &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= sorted[k] && sorted[k] < 100)) &&
          (forall (bucket : Z),
            (0 <= bucket && bucket < 100) =>
            (0 <= positions[bucket] && positions[bucket] <= n@pre)) &&
          (i >= 0 => 1 <= positions[input[i]]) &&
          (forall (k : Z),
            (n@pre <= k && k < 100) => output_mixed[k] == None) &&
          CountingPlacementProgress(
            input, positions, bucket_ends, output_mixed, sorted, i) &&
          IntArray::full(a, n@pre, input) *
          IntArray::mixed_full(output, 100, output_mixed) *
          IntArray::full(count, 100, positions)
    */
    for (int i = n - 1; i >= 0; --i) {
        /*@ Given positions */
        int value = a[i];
        /*@ 0 <= value && value < 100 &&
            value == Znth(i, input, 0) &&
            1 <= Znth(value, positions, 0) &&
            Znth(value, positions, 0) <= n@pre by local */
        --count[value];
        /*@ 0 <= Znth(
                     value,
                     replace_Znth(
                       value, Znth(value, positions, 0) - 1, positions),
                     0) &&
            Znth(
              value,
              replace_Znth(
                value, Znth(value, positions, 0) - 1, positions),
              0) < 100 by local */
        output[count[value]] = value;
    }

    /*@ Assert
        exists sorted bucket_starts,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(sorted) == n@pre &&
          Zlength(bucket_starts) == 100 &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= sorted[k] && sorted[k] < 100)) &&
          CountingSorted(input, sorted) &&
          IntArray::full(a, n@pre, input) *
          IntArray::seg(output, 0, n@pre, sorted) *
          IntArray::undef_seg(output, n@pre, 100) *
          IntArray::full(count, 100, bucket_starts)
    */
    /*@ Inv Assert
        exists sorted live bucket_starts,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(sorted) == n@pre &&
          Zlength(live) == n@pre &&
          Zlength(bucket_starts) == 100 &&
          0 <= i && i <= n@pre &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
            (0 <= sorted[k] && sorted[k] < 100)) &&
          CountingSorted(input, sorted) &&
          CountingCopyProgress(input, sorted, live, i) &&
          IntArray::full(a, n@pre, live) *
          IntArray::seg(output, 0, n@pre, sorted) *
          IntArray::undef_seg(output, n@pre, 100) *
          IntArray::full(count, 100, bucket_starts)
    */
    for (int i = 0; i < n; ++i) {
        a[i] = output[i];
    }

    /*@ Assert
        exists sorted,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(sorted) == n@pre &&
          CountingSorted(input, sorted) &&
          IntArray::full(a, n@pre, sorted) *
          IntArray::undef_full(output, 100) *
          IntArray::undef_full(count, 100)
    */
}
