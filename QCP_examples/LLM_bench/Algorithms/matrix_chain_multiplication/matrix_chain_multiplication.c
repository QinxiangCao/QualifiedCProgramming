/*
 * Matrix-chain multiplication (CLRS interval dynamic programming).
 *
 * Matrix i has dimensions dimensions[i] by dimensions[i + 1].  The function
 * keeps its dynamic-programming workspace in a local array.
 * The verified interface bounds matrix_count and the dimensions so that every
 * scalar-multiplication count below fits in a signed 32-bit int.
 */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (MatrixChainOptimalCost : list Z -> Z -> Z -> Prop)
      (MatrixChainTableComplete : list Z -> list Z -> Z -> Prop)
      (MatrixChainLengthsComplete : list Z -> list Z -> Z -> Z -> Prop)
      (MatrixChainLeftComplete : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (MatrixChainSplitMinimum : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MatrixChainIntervalMinimum : list Z -> Z -> Z -> Z -> Prop)
      (MatrixChainSplitCandidate : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib */

int matrixChainMinCost(int *dimensions, int matrix_count)
/*@ With (dimensions_l : list Z)
    Require
      1 <= matrix_count && matrix_count <= 8 &&
      Zlength(dimensions_l) == matrix_count + 1 &&
      Zlength(dimensions_l) == matrix_count + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
      IntArray::full(dimensions, matrix_count + 1, dimensions_l)
    Ensure
      MatrixChainOptimalCost(dimensions_l, matrix_count, __return) &&
      IntArray::full(dimensions, matrix_count + 1, dimensions_l)
 */
{
  int cost[64];

  int width = matrix_count;

  /* A one-matrix product needs no scalar multiplications.  Clearing the whole
   * table gives defined values to every internal DP cell. */
  /*@ Inv Assert
      exists cost_l,
      dimensions == dimensions@pre && 
      matrix_count == matrix_count@pre && width == matrix_count@pre &&
      1 <= matrix_count@pre && matrix_count@pre <= 8 &&
      Zlength(dimensions_l) == matrix_count@pre + 1 &&
      0 <= i && i <= matrix_count@pre * width &&
      Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
      Zlength(cost_l) == i && Forall(eq(0), cost_l) &&
      IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
      IntArray::seg(cost, 0, i, cost_l) *
      IntArray::undef_seg(cost, i, matrix_count@pre * width) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
  for (int i = 0; i < matrix_count * width; ++i) {
    cost[i] = 0;
  }

  /* After finishing a chain length, every shorter interval already contains
   * its minimum cost, so it is available to each candidate split below. */
  /*@ Inv Assert
      exists cost_l,
      dimensions == dimensions@pre && 
      matrix_count == matrix_count@pre && width == matrix_count@pre &&
      1 <= matrix_count@pre && matrix_count@pre <= 8 &&
      Zlength(dimensions_l) == matrix_count@pre + 1 &&
      Zlength(cost_l) == matrix_count@pre * width &&
      2 <= chain_length && chain_length <= matrix_count@pre + 1 &&
      Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
      Forall(Z::le(0), cost_l) && Forall(Z::ge(7000000), cost_l) &&
      1 <= chain_length && MatrixChainLengthsComplete(dimensions_l, cost_l, matrix_count@pre, chain_length) &&
      IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
      IntArray::full(cost, matrix_count@pre * width, cost_l) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
  for (int chain_length = 2;
       chain_length <= matrix_count;
       ++chain_length) {
    /*@ Inv Assert
        exists cost_l,
        dimensions == dimensions@pre && 
        matrix_count == matrix_count@pre && width == matrix_count@pre &&
        1 <= matrix_count@pre && matrix_count@pre <= 8 &&
        Zlength(dimensions_l) == matrix_count@pre + 1 &&
        Zlength(cost_l) == matrix_count@pre * width &&
        2 <= chain_length && chain_length <= matrix_count@pre &&
        0 <= left && left <= matrix_count@pre - chain_length + 1 &&
        Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
        Forall(Z::le(0), cost_l) && Forall(Z::ge(7000000), cost_l) &&
        1 <= chain_length && MatrixChainLeftComplete(dimensions_l, cost_l, matrix_count@pre, chain_length, left) &&
        IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
        IntArray::full(cost, matrix_count@pre * width, cost_l) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
    for (int left = 0;
         left + chain_length <= matrix_count;
         ++left) {
      int right = left + chain_length - 1;

      /* Use the leftmost split as a real initial candidate. */
      /*@ Assert
          exists cost_l,
          dimensions == dimensions@pre && 
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
          Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
          Forall(Z::le(0), cost_l) && Forall(Z::ge(7000000), cost_l) &&
          1 <= chain_length && MatrixChainLeftComplete(dimensions_l, cost_l, matrix_count@pre, chain_length, left) &&
          IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
          IntArray::full(cost, matrix_count@pre * width, cost_l) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
      int best = cost[left * width + left]
               + cost[(left + 1) * width + right]
               + dimensions[left] * dimensions[left + 1]
               * dimensions[right + 1];

      /*@ Inv Assert
          exists cost_l,
          dimensions == dimensions@pre && 
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
          Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
          Forall(Z::le(0), cost_l) && Forall(Z::ge(7000000), cost_l) &&
          1 <= chain_length && MatrixChainSplitMinimum(dimensions_l, cost_l, matrix_count@pre, width, chain_length, left, split, best) &&
          IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
          IntArray::full(cost, matrix_count@pre * width, cost_l) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
      for (int split = left + 1; split < right; ++split) {
        /*@ Assert
            exists cost_l,
            dimensions == dimensions@pre && 
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
            Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
            Forall(Z::le(0), cost_l) && Forall(Z::ge(7000000), cost_l) &&
            1 <= chain_length && MatrixChainSplitMinimum(dimensions_l, cost_l, matrix_count@pre, width, chain_length, left, split, best) &&
            IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
            IntArray::full(cost, matrix_count@pre * width, cost_l) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
        int candidate = cost[left * width + split]
                      + cost[(split + 1) * width + right]
                      + dimensions[left] * dimensions[split + 1]
                      * dimensions[right + 1];
        /*@ Assert
            exists cost_l,
            dimensions == dimensions@pre && 
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
            Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
            Forall(Z::le(0), cost_l) && Forall(Z::ge(7000000), cost_l) &&
            MatrixChainSplitCandidate
              (dimensions_l, cost_l, width, left, right, split, candidate) &&
            1 <= chain_length && MatrixChainSplitMinimum(dimensions_l, cost_l, matrix_count@pre, width, chain_length, left, split, best) &&
            IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
            IntArray::full(cost, matrix_count@pre * width, cost_l) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
        if (candidate < best) {
          best = candidate;
        }
      }

      /*@ Assert
          exists cost_l,
          dimensions == dimensions@pre && 
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
          Zlength(dimensions_l) == matrix_count@pre + 1 && Forall(Z::le(1), dimensions_l) && Forall(Z::ge(100), dimensions_l) &&
          Forall(Z::le(0), cost_l) && Forall(Z::ge(7000000), cost_l) &&
          1 <= chain_length && MatrixChainSplitMinimum(dimensions_l, cost_l, matrix_count@pre, width, chain_length, left, right, best) &&
          MatrixChainIntervalMinimum(dimensions_l, left, right, best) &&
          IntArray::full(dimensions, matrix_count@pre + 1, dimensions_l) *
          IntArray::full(cost, matrix_count@pre * width, cost_l) *
      IntArray::undef_seg(cost, matrix_count@pre * matrix_count@pre, 64)
   */
      cost[left * width + right] = best;
    }
  }


  int result = cost[matrix_count - 1];
  /*@ Assert
      dimensions == dimensions@pre && matrix_count == matrix_count@pre &&
      MatrixChainOptimalCost(dimensions_l, matrix_count@pre, result) &&
      IntArray::full(dimensions@pre, matrix_count@pre + 1, dimensions_l) *
      IntArray::undef_full(cost, 64) *
      has_int_permission(&width)
   */
  return result;
}
