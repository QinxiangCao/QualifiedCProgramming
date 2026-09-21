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
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (HuffmanOptimalCost : list Z -> Z -> Prop)
      (HuffmanProgress : list Z -> list Z -> Z -> Z -> Prop)
      (HuffmanMinScan : list Z -> Z -> Z -> Prop)
      (HuffmanFirstHeld : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (HuffmanPairReady : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib */

int huffman_cost(int *weights, int n)
/*@ With (weights_l : list Z)
    Require
      1 <= n && n <= 8 &&
      Zlength(weights_l) == n &&
      Forall(Z::le(1), weights_l) && Forall(Z::ge(1000), weights_l) &&
      IntArray::full(weights, n, weights_l)
    Ensure
      HuffmanOptimalCost(weights_l, __return) &&
      IntArray::full(weights, n, weights_l)
 */
{
  int work[8];
  /*@ Inv Assert
      exists copied remaining,
        weights == weights@pre && n == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Zlength(weights_l) == n@pre &&
        Forall(Z::le(1), weights_l) && Forall(Z::ge(1000), weights_l) &&
        weights_l == app(copied, remaining) &&
        Zlength(copied) == i &&
        0 <= i && i <= n@pre &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::seg(work, 0, i, copied) *
        IntArray::undef_seg(work, i, n@pre) *
        IntArray::undef_seg(work, n@pre, 8)
   */
  for (int i = 0; i < n; ++i) {
    work[i] = weights[i];
  }

  int active = n;
  int total = 0;

  /*@ Inv Assert
      exists work_l,
        weights == weights@pre && n == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Zlength(weights_l) == n@pre &&
        Zlength(work_l) == n@pre &&
        Forall(Z::le(1), weights_l) && Forall(Z::ge(1000), weights_l) &&
        1 <= active && active <= n@pre &&
        0 <= total && total <= 56000 &&
        Forall(Z::le(1), sublist(0, active, work_l)) &&
          Forall(Z::ge(8000), sublist(0, active, work_l)) &&
        HuffmanProgress(weights_l, work_l, active, total) &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::full(work, n@pre, work_l) *
          IntArray::undef_seg(work, n@pre, 8)
   */
  while (active > 1) {
    int first = 0;
    /*@ Inv Assert
        exists work_l,
          weights == weights@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          Zlength(weights_l) == n@pre &&
          Zlength(work_l) == n@pre &&
          Forall(Z::le(1), weights_l) && Forall(Z::ge(1000), weights_l) &&
          2 <= active && active <= n@pre &&
          1 <= i && i <= active && i <= n@pre &&
          0 <= first && first < i && first < n@pre &&
          0 <= total && total <= 56000 &&
          Forall(Z::le(1), sublist(0, active, work_l)) &&
          Forall(Z::ge(8000), sublist(0, active, work_l)) &&
          HuffmanProgress(weights_l, work_l, active, total) &&
          HuffmanMinScan(work_l, i, first) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(work, n@pre, work_l) *
          IntArray::undef_seg(work, n@pre, 8)
     */
    for (int i = 1; i < active; ++i) {
      /*@ 0 <= i && i < n@pre */
      if (work[i] < work[first]) {
        first = i;
      }
    }

    int x = work[first];
    --active;

    work[first] = work[active];


    int second = 0;
    /*@ Inv Assert
        exists work_l,
          weights == weights@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          Zlength(weights_l) == n@pre &&
          Zlength(work_l) == n@pre &&
          Forall(Z::le(1), weights_l) && Forall(Z::ge(1000), weights_l) &&
          1 <= active && active < n@pre &&
          1 <= i && i <= active && i < n@pre &&
          0 <= first && first < n@pre &&
          0 <= second && second < i && second < n@pre &&
          1 <= x && x <= 8000 &&
          0 <= total && total <= 56000 &&
          Forall(Z::le(1), sublist(0, active, work_l)) &&
          Forall(Z::ge(8000), sublist(0, active, work_l)) &&
          HuffmanFirstHeld(weights_l, work_l, active, x, total) &&
          HuffmanMinScan(work_l, i, second) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(work, n@pre, work_l) *
          IntArray::undef_seg(work, n@pre, 8)
     */
    for (int i = 1; i < active; ++i) {
      if (work[i] < work[second]) {
        second = i;
      }
    }

    int y = work[second];
    --active;

    work[second] = work[active];


    int merged = x + y;
    total += merged;
    work[active] = merged;
    ++active;
  }

  /*@ Assert
        weights == weights@pre && n == n@pre &&
        active == 1 &&
        HuffmanOptimalCost(weights_l, total) &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::undef_full(work, 8)
   */
  return total;
}
