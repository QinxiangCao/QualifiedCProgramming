/*
 * Huffman encoding: minimum weighted path length of a binary prefix code.
 *
 * Repeatedly merging the two smallest live weights constructs a Huffman tree.
 * The sum of all merge weights is that tree's weighted path length and is
 * minimum among all full binary prefix-code trees over the input frequencies.
 *
 * This verification-oriented implementation uses a fresh selection scan for
 * each of the two minima.  Removing a selected item is done by moving the last
 * live item into its slot, so only the prefix work[0..active) is live.
 */

/*@ Extern Coq
      (HuffmanInputBounded : list Z -> Prop)
      (HuffmanOptimalCost : list Z -> Z -> Prop)
      (HuffmanScratchFinal : list Z -> list Z -> Prop)
      (HuffmanProgress : list Z -> list Z -> Z -> Z -> Prop)
      (HuffmanMinScan : list Z -> Z -> Z -> Prop)
      (HuffmanFirstHeld : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (HuffmanPairReady : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib */

int huffman_cost(int *weights, int n, int *work)
/*@ With (weights_l : list Z)
    Require
      1 <= n && n <= 8 &&
      Zlength(weights_l) == n &&
      HuffmanInputBounded(weights_l) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::undef_full(work, n)
    Ensure
      exists work_l,
        Zlength(work_l) == n &&
        HuffmanOptimalCost(weights_l, __return) &&
        HuffmanScratchFinal(weights_l, work_l) &&
        0 <= __return && __return <= 56000 &&
        IntArray::full(weights, n, weights_l) *
        IntArray::full(work, n, work_l)
 */
{
  /*@ Inv Assert
      exists copied remaining,
        weights == weights@pre && work == work@pre && n == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Zlength(weights_l) == n@pre &&
        HuffmanInputBounded(weights_l) &&
        weights_l == app(copied, remaining) &&
        Zlength(copied) == i &&
        0 <= i && i <= n@pre &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::seg(work, 0, i, copied) *
        IntArray::undef_seg(work, i, n@pre)
   */
  for (int i = 0; i < n; ++i) {
    work[i] = weights[i];
  }

  int active = n;
  int total = 0;

  /*@ Inv Assert
      exists work_l,
        weights == weights@pre && work == work@pre && n == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Zlength(weights_l) == n@pre &&
        Zlength(work_l) == n@pre &&
        HuffmanInputBounded(weights_l) &&
        1 <= active && active <= n@pre &&
        0 <= total && total <= 56000 &&
        (forall (k : Z),
          0 <= k && k < active =>
          1 <= Znth(k, work_l, 0) && Znth(k, work_l, 0) <= 8000) &&
        HuffmanProgress(weights_l, work_l, active, total) &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::full(work, n@pre, work_l)
   */
  while (active > 1) {
    int first = 0;
    /*@ Inv Assert
        exists work_l,
          weights == weights@pre && work == work@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          Zlength(weights_l) == n@pre &&
          Zlength(work_l) == n@pre &&
          HuffmanInputBounded(weights_l) &&
          2 <= active && active <= n@pre &&
          1 <= i && i <= active && i <= n@pre &&
          0 <= first && first < i && first < n@pre &&
          0 <= total && total <= 56000 &&
          (forall (k : Z),
            0 <= k && k < active =>
            1 <= Znth(k, work_l, 0) && Znth(k, work_l, 0) <= 8000) &&
          HuffmanProgress(weights_l, work_l, active, total) &&
          HuffmanMinScan(work_l, i, first) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(work, n@pre, work_l)
     */
    for (int i = 1; i < active; ++i) {
      /*@ 0 <= i && i < n@pre */
      if (work[i] < work[first]) {
        first = i;
      }
    }

    int x = work[first];
    --active;
    /*@ 0 <= active && active < n@pre */
    work[first] = work[active];

    /*@ Assert
        exists work_l,
          weights == weights@pre && work == work@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          Zlength(weights_l) == n@pre &&
          Zlength(work_l) == n@pre &&
          HuffmanInputBounded(weights_l) &&
          1 <= active && active < n@pre &&
          0 <= first && first < n@pre &&
          1 <= x && x <= 8000 &&
          0 <= total && total <= 56000 &&
          (forall (k : Z),
            0 <= k && k < active =>
            1 <= Znth(k, work_l, 0) && Znth(k, work_l, 0) <= 8000) &&
          HuffmanFirstHeld(weights_l, work_l, active, x, total) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(work, n@pre, work_l)
     */
    int second = 0;
    /*@ Inv Assert
        exists work_l,
          weights == weights@pre && work == work@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          Zlength(weights_l) == n@pre &&
          Zlength(work_l) == n@pre &&
          HuffmanInputBounded(weights_l) &&
          1 <= active && active < n@pre &&
          1 <= i && i <= active && i < n@pre &&
          0 <= first && first < n@pre &&
          0 <= second && second < i && second < n@pre &&
          1 <= x && x <= 8000 &&
          0 <= total && total <= 56000 &&
          (forall (k : Z),
            0 <= k && k < active =>
            1 <= Znth(k, work_l, 0) && Znth(k, work_l, 0) <= 8000) &&
          HuffmanFirstHeld(weights_l, work_l, active, x, total) &&
          HuffmanMinScan(work_l, i, second) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(work, n@pre, work_l)
     */
    for (int i = 1; i < active; ++i) {
      if (work[i] < work[second]) {
        second = i;
      }
    }

    int y = work[second];
    --active;
    /*@ 0 <= active && active < n@pre */
    work[second] = work[active];

    /*@ Assert
        exists work_l,
          weights == weights@pre && work == work@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          Zlength(weights_l) == n@pre &&
          Zlength(work_l) == n@pre &&
          HuffmanInputBounded(weights_l) &&
          0 <= active && active <= n@pre - 2 &&
          0 <= first && first < n@pre &&
          0 <= second && second < n@pre &&
          1 <= x && x <= 8000 &&
          1 <= y && y <= 8000 &&
          x + y <= 8000 &&
          0 <= total && total + x + y <= 56000 &&
          (forall (k : Z),
            0 <= k && k < active =>
            1 <= Znth(k, work_l, 0) && Znth(k, work_l, 0) <= 8000) &&
          HuffmanPairReady(weights_l, work_l, active, x, y, total) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(work, n@pre, work_l)
     */
    int merged = x + y;
    total += merged;
    work[active] = merged;
    ++active;
  }

  /*@ Assert
      exists final_work_l,
        weights == weights@pre && work == work@pre && n == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Zlength(weights_l) == n@pre &&
        Zlength(final_work_l) == n@pre &&
        active == 1 &&
        0 <= total && total <= 56000 &&
        HuffmanOptimalCost(weights_l, total) &&
        HuffmanScratchFinal(weights_l, final_work_l) &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::full(work, n@pre, final_work_l)
   */
  return total;
}
