/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::gt : Z -> Z -> Prop)
      (eq : {A} -> A -> A -> Prop)
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
      Forall(Z::le(0), input) && Forall(Z::gt(100), input) &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
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
          Forall(Z::le(0), input) && Forall(Z::gt(100), input) &&
          Forall(eq(None), output_mixed) &&
          CountingZeroedPrefix(count_mixed, value) &&
          IntArray::full(a, n@pre, input) *
          IntArray::mixed_full(output, 100, output_mixed) *
          IntArray::mixed_full(count, 100, count_mixed)
    */
    for (int value = 0; value < 100; ++value) {
        count[value] = 0;
    }

    /*@ Inv Assert
        exists output_mixed counts,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(output_mixed) == 100 &&
          Zlength(counts) == 100 &&
          0 <= i && i <= n@pre &&
          Forall(Z::le(0), input) && Forall(Z::gt(100), input) &&
          Forall(Z::le(0), counts) && Forall(Z::ge(i), counts) &&
          Forall(eq(None), output_mixed) &&
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
          Forall(Z::le(0), input) && Forall(Z::gt(100), input) &&
          Forall(Z::le(0), positions) && Forall(Z::ge(n@pre), positions) &&
          (value < 100 =>
            positions[value] + positions[value - 1] <= n@pre) &&
          Forall(eq(None), output_mixed) &&
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
          Forall(Z::le(0), input) && Forall(Z::gt(100), input) &&
          Forall(Z::le(0), sorted) && Forall(Z::gt(100), sorted) &&
          Forall(Z::le(0), positions) && Forall(Z::ge(n@pre), positions) &&
          (i >= 0 => 1 <= positions[input[i]]) &&
          Forall(eq(None), sublist(n@pre, 100, output_mixed)) &&
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

    /*@ Inv Assert
        exists sorted live bucket_starts,
          a == a@pre && n == n@pre &&
          0 <= n@pre && n@pre <= 100 &&
          Zlength(input) == n@pre &&
          Zlength(sorted) == n@pre &&
          Zlength(live) == n@pre &&
          Zlength(bucket_starts) == 100 &&
          0 <= i && i <= n@pre &&
          Forall(Z::le(0), sorted) && Forall(Z::gt(100), sorted) &&
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
