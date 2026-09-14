/*
 * Matrix-chain multiplication (CLRS interval dynamic programming).
 *
 * Matrix i has dimensions dimensions[i] by dimensions[i + 1].  The caller
 * supplies matrix_count * matrix_count integers in cost as the DP workspace.
 * The verified interface bounds matrix_count and the dimensions so that every
 * scalar-multiplication count below fits in a signed 32-bit int.
 */
/*@ Extern Coq
      (MatrixChainDimensionsBounded : list Z -> Z -> Prop)
      (MatrixChainIntervalMinimum : list Z -> Z -> Z -> Z -> Prop)
      (MatrixChainMinimumCost : list Z -> Z -> Z -> Prop)
      (MatrixChainTableResult : list Z -> list Z -> Z -> Prop)
      (MatrixChainZeroPrefix : list Z -> Z -> Prop)
      (MatrixChainTableValuesBounded : list Z -> Prop)
      (MatrixChainLengthsDone : list Z -> list Z -> Z -> Z -> Prop)
      (MatrixChainLeftProgress : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (MatrixChainSplitCandidate : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MatrixChainSplitProgress : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib */

int matrixChainMinCost(int *dimensions, int matrix_count, int *cost)
/*@ With (dimensions_l : list Z)
    Require
      1 <= matrix_count && matrix_count <= 8 &&
      Zlength(dimensions_l) == matrix_count + 1 &&
      MatrixChainDimensionsBounded(dimensions_l, matrix_count) &&
      IntArray::full(dimensions, matrix_count + 1, dimensions_l) *
      IntArray::undef_full(cost, matrix_count * matrix_count)
    Ensure
      exists cost_l,
      MatrixChainTableResult(dimensions_l, cost_l, matrix_count) &&
      MatrixChainMinimumCost(dimensions_l, matrix_count, __return) &&
      __return == cost_l[matrix_count - 1] &&
      0 <= __return && __return <= 7000000 &&
      IntArray::full(dimensions, matrix_count + 1, dimensions_l) *
      IntArray::full(cost, matrix_count * matrix_count, cost_l)
 */
{
  int width = matrix_count;

  /* A one-matrix product needs no scalar multiplications.  Clearing the whole
   * table also gives defined values to the caller's complete workspace. */
  /*@ Inv Assert
      exists cost_l,
      dimensions == dimensions@pre && cost == cost@pre &&
      matrix_count == matrix_count@pre && width == matrix_count@pre &&
      1 <= matrix_count@pre && matrix_count@pre <= 8 &&
      Zlength(dimensions_l) == matrix_count@pre + 1 &&
      0 <= i && i <= matrix_count@pre * width &&
      MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
      MatrixChainZeroPrefix(cost_l, i) &&
      IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
      IntArray::seg(cost, 0, i, cost_l) *
      IntArray::undef_seg(cost, i, matrix_count@pre * width)
   */
  for (int i = 0; i < matrix_count * width; ++i) {
    cost[i] = 0;
  }

  /* After finishing a chain length, every shorter interval already contains
   * its minimum cost, so it is available to each candidate split below. */
  /*@ Assert
      exists cost_l,
      dimensions == dimensions@pre && cost == cost@pre &&
      matrix_count == matrix_count@pre && width == matrix_count@pre &&
      1 <= matrix_count@pre && matrix_count@pre <= 8 &&
      Zlength(dimensions_l) == matrix_count@pre + 1 &&
      Zlength(cost_l) == matrix_count@pre * width &&
      MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
      MatrixChainTableValuesBounded(cost_l) &&
      MatrixChainLengthsDone(dimensions_l, cost_l, matrix_count@pre, 2) &&
      IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
      IntArray::full(cost, matrix_count@pre * width, cost_l)
   */
  /*@ Inv Assert
      exists cost_l,
      dimensions == dimensions@pre && cost == cost@pre &&
      matrix_count == matrix_count@pre && width == matrix_count@pre &&
      1 <= matrix_count@pre && matrix_count@pre <= 8 &&
      Zlength(dimensions_l) == matrix_count@pre + 1 &&
      Zlength(cost_l) == matrix_count@pre * width &&
      2 <= chain_length && chain_length <= matrix_count@pre + 1 &&
      MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
      MatrixChainTableValuesBounded(cost_l) &&
      MatrixChainLengthsDone
        (dimensions_l, cost_l, matrix_count@pre, chain_length) &&
      IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
      IntArray::full(cost, matrix_count@pre * width, cost_l)
   */
  for (int chain_length = 2;
       chain_length <= matrix_count;
       ++chain_length) {
    /*@ Inv Assert
        exists cost_l,
        dimensions == dimensions@pre && cost == cost@pre &&
        matrix_count == matrix_count@pre && width == matrix_count@pre &&
        1 <= matrix_count@pre && matrix_count@pre <= 8 &&
        Zlength(dimensions_l) == matrix_count@pre + 1 &&
        Zlength(cost_l) == matrix_count@pre * width &&
        2 <= chain_length && chain_length <= matrix_count@pre &&
        0 <= left && left <= matrix_count@pre - chain_length + 1 &&
        MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
        MatrixChainTableValuesBounded(cost_l) &&
        MatrixChainLeftProgress
          (dimensions_l, cost_l, matrix_count@pre, chain_length, left) &&
        IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
        IntArray::full(cost, matrix_count@pre * width, cost_l)
     */
    for (int left = 0;
         left + chain_length <= matrix_count;
         ++left) {
      int right = left + chain_length - 1;

      /* Use the leftmost split as a real initial candidate. */
      /*@ Assert
          exists cost_l,
          dimensions == dimensions@pre && cost == cost@pre &&
          matrix_count == matrix_count@pre && width == matrix_count@pre &&
          1 <= matrix_count@pre && matrix_count@pre <= 8 &&
          2 <= chain_length && chain_length <= matrix_count@pre &&
          0 <= left && left + chain_length <= matrix_count@pre &&
          right == left + chain_length - 1 &&
          left < right && right < matrix_count@pre &&
          0 <= left * width + left &&
          left * width + left < matrix_count@pre * width &&
          0 <= (left + 1) * width + right &&
          (left + 1) * width + right < matrix_count@pre * width &&
          0 <= left && left < matrix_count@pre + 1 &&
          0 <= left + 1 && left + 1 < matrix_count@pre + 1 &&
          0 <= right + 1 && right + 1 < matrix_count@pre + 1 &&
          Zlength(dimensions_l) == matrix_count@pre + 1 &&
          Zlength(cost_l) == matrix_count@pre * width &&
          0 <= cost_l[left * width + left] &&
          cost_l[left * width + left] <= 7000000 &&
          0 <= cost_l[(left + 1) * width + right] &&
          cost_l[(left + 1) * width + right] <= 7000000 &&
          1 <= dimensions_l[left] && dimensions_l[left] <= 100 &&
          1 <= dimensions_l[left + 1] && dimensions_l[left + 1] <= 100 &&
          1 <= dimensions_l[right + 1] && dimensions_l[right + 1] <= 100 &&
          MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
          MatrixChainTableValuesBounded(cost_l) &&
          MatrixChainLeftProgress
            (dimensions_l, cost_l, matrix_count@pre, chain_length, left) &&
          IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
          IntArray::full(cost, matrix_count@pre * width, cost_l)
       */
      int best = cost[left * width + left]
               + cost[(left + 1) * width + right]
               + dimensions[left] * dimensions[left + 1]
               * dimensions[right + 1];

      /*@ Inv Assert
          exists cost_l,
          dimensions == dimensions@pre && cost == cost@pre &&
          matrix_count == matrix_count@pre && width == matrix_count@pre &&
          1 <= matrix_count@pre && matrix_count@pre <= 8 &&
          2 <= chain_length && chain_length <= matrix_count@pre &&
          0 <= left && left + chain_length <= matrix_count@pre &&
          right == left + chain_length - 1 &&
          left < right && right < matrix_count@pre &&
          left + 1 <= split && split <= right &&
          0 <= best && best <= 7000000 &&
          Zlength(dimensions_l) == matrix_count@pre + 1 &&
          Zlength(cost_l) == matrix_count@pre * width &&
          MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
          MatrixChainTableValuesBounded(cost_l) &&
          MatrixChainSplitProgress
            (dimensions_l, cost_l, matrix_count@pre, width,
             chain_length, left, split, best) &&
          IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
          IntArray::full(cost, matrix_count@pre * width, cost_l)
       */
      for (int split = left + 1; split < right; ++split) {
        /*@ Assert
            exists cost_l,
            dimensions == dimensions@pre && cost == cost@pre &&
            matrix_count == matrix_count@pre && width == matrix_count@pre &&
            1 <= matrix_count@pre && matrix_count@pre <= 8 &&
            2 <= chain_length && chain_length <= matrix_count@pre &&
            0 <= left && left + chain_length <= matrix_count@pre &&
            right == left + chain_length - 1 &&
            left < right && right < matrix_count@pre &&
            left + 1 <= split && split < right &&
            0 <= left * width + split &&
            left * width + split < matrix_count@pre * width &&
            0 <= (split + 1) * width + right &&
            (split + 1) * width + right < matrix_count@pre * width &&
            0 <= left && left < matrix_count@pre + 1 &&
            0 <= split + 1 && split + 1 < matrix_count@pre + 1 &&
            0 <= right + 1 && right + 1 < matrix_count@pre + 1 &&
            0 <= best && best <= 7000000 &&
            Zlength(dimensions_l) == matrix_count@pre + 1 &&
            Zlength(cost_l) == matrix_count@pre * width &&
            0 <= cost_l[left * width + split] &&
            cost_l[left * width + split] <= 7000000 &&
            0 <= cost_l[(split + 1) * width + right] &&
            cost_l[(split + 1) * width + right] <= 7000000 &&
            1 <= dimensions_l[left] && dimensions_l[left] <= 100 &&
            1 <= dimensions_l[split + 1] &&
            dimensions_l[split + 1] <= 100 &&
            1 <= dimensions_l[right + 1] &&
            dimensions_l[right + 1] <= 100 &&
            MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
            MatrixChainTableValuesBounded(cost_l) &&
            MatrixChainSplitProgress
              (dimensions_l, cost_l, matrix_count@pre, width,
               chain_length, left, split, best) &&
            IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
            IntArray::full(cost, matrix_count@pre * width, cost_l)
         */
        int candidate = cost[left * width + split]
                      + cost[(split + 1) * width + right]
                      + dimensions[left] * dimensions[split + 1]
                      * dimensions[right + 1];
        /*@ Assert
            exists cost_l,
            dimensions == dimensions@pre && cost == cost@pre &&
            matrix_count == matrix_count@pre && width == matrix_count@pre &&
            1 <= matrix_count@pre && matrix_count@pre <= 8 &&
            2 <= chain_length && chain_length <= matrix_count@pre &&
            0 <= left && left + chain_length <= matrix_count@pre &&
            right == left + chain_length - 1 &&
            left < right && right < matrix_count@pre &&
            left + 1 <= split && split < right &&
            0 <= best && best <= 7000000 &&
            0 <= candidate && candidate <= 7000000 &&
            Zlength(dimensions_l) == matrix_count@pre + 1 &&
            Zlength(cost_l) == matrix_count@pre * width &&
            MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
            MatrixChainTableValuesBounded(cost_l) &&
            MatrixChainSplitCandidate
              (dimensions_l, cost_l, width, left, right, split, candidate) &&
            MatrixChainSplitProgress
              (dimensions_l, cost_l, matrix_count@pre, width,
               chain_length, left, split, best) &&
            IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
            IntArray::full(cost, matrix_count@pre * width, cost_l)
         */
        if (candidate < best) {
          best = candidate;
        }
      }

      /*@ Assert
          exists cost_l,
          dimensions == dimensions@pre && cost == cost@pre &&
          matrix_count == matrix_count@pre && width == matrix_count@pre &&
          1 <= matrix_count@pre && matrix_count@pre <= 8 &&
          2 <= chain_length && chain_length <= matrix_count@pre &&
          0 <= left && left + chain_length <= matrix_count@pre &&
          right == left + chain_length - 1 &&
          left < right && right < matrix_count@pre &&
          0 <= best && best <= 7000000 &&
          0 <= left * width + right &&
          left * width + right < matrix_count@pre * width &&
          Zlength(dimensions_l) == matrix_count@pre + 1 &&
          Zlength(cost_l) == matrix_count@pre * width &&
          MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
          MatrixChainTableValuesBounded(cost_l) &&
          MatrixChainSplitProgress
            (dimensions_l, cost_l, matrix_count@pre, width,
             chain_length, left, right, best) &&
          MatrixChainIntervalMinimum(dimensions_l, left, right, best) &&
          IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
          IntArray::full(cost, matrix_count@pre * width, cost_l)
       */
      cost[left * width + right] = best;
    }
  }

  /*@ Assert
      exists cost_l,
      dimensions == dimensions@pre && cost == cost@pre &&
      matrix_count == matrix_count@pre && width == matrix_count@pre &&
      1 <= matrix_count@pre && matrix_count@pre <= 8 &&
      0 <= matrix_count@pre - 1 &&
      matrix_count@pre - 1 < matrix_count@pre * width &&
      Zlength(dimensions_l) == matrix_count@pre + 1 &&
      Zlength(cost_l) == matrix_count@pre * width &&
      0 <= cost_l[matrix_count@pre - 1] &&
      cost_l[matrix_count@pre - 1] <= 7000000 &&
      MatrixChainDimensionsBounded(dimensions_l, matrix_count@pre) &&
      MatrixChainTableValuesBounded(cost_l) &&
      MatrixChainLengthsDone
        (dimensions_l, cost_l, matrix_count@pre, matrix_count@pre + 1) &&
      MatrixChainTableResult(dimensions_l, cost_l, matrix_count@pre) &&
      MatrixChainMinimumCost
        (dimensions_l, matrix_count@pre,
         cost_l[matrix_count@pre - 1]) &&
      IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
      IntArray::full(cost, matrix_count@pre * width, cost_l)
   */
  return cost[matrix_count - 1];
}
