/*@ Extern Coq
      (FenwickLowbit : Z -> Z)
      (FenwickNodeLo : Z -> Z)
      (FenwickNodeSum : list Z -> Z -> Z)
      (FenwickPrefixSum : list Z -> Z -> Z)
      (FenwickAddArray : list Z -> Z -> Z -> list Z)
      (FenwickRep : list Z -> list Z -> Z -> Prop)
      (FenwickIntervalsIntSafe : list Z -> Z -> Prop)
      (FenwickAddProgress : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (FenwickQueryState : list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib */

int lowbit(int x)
/*@ Require 1 <= x && x <= INT_MAX
    Ensure
      __return == FenwickLowbit(x) &&
      1 <= __return && __return <= x
 */
{
  return x & (-x);
}

void add(int *bit, int n, int pos, int delta)
/*@ With (a : list Z) (bit_l : list Z)
    Require
      1 <= n && 2 * n <= INT_MAX &&
      1 <= pos && pos <= n &&
      FenwickRep(a, bit_l, n) &&
      FenwickIntervalsIntSafe(a, n) &&
      FenwickIntervalsIntSafe(FenwickAddArray(a, pos, delta), n) &&
      IntArray::full(bit, n + 1, bit_l)
    Ensure
      exists bit_l1,
        FenwickRep(FenwickAddArray(a, pos, delta), bit_l1, n) &&
        Znth(0, bit_l1, 0) == Znth(0, bit_l, 0) &&
        IntArray::full(bit, n + 1, bit_l1)
 */
{
  /*@ Inv Assert
      exists bit_cur,
        bit == bit@pre && n == n@pre && delta == delta@pre &&
        1 <= n@pre && 2 * n@pre <= INT_MAX &&
        1 <= pos@pre && pos@pre <= n@pre &&
        1 <= pos && pos <= 2 * n@pre &&
        FenwickRep(a, bit_l, n@pre) &&
        FenwickIntervalsIntSafe(a, n@pre) &&
        FenwickIntervalsIntSafe(
          FenwickAddArray(a, pos@pre, delta@pre), n@pre) &&
        FenwickAddProgress(
          bit_l, bit_cur, n@pre, pos@pre, pos, delta@pre) &&
        IntArray::full(bit@pre, n@pre + 1, bit_cur)
   */
  while (pos <= n) {
    bit[pos] += delta;
    pos += lowbit(pos);
  }
}

int query(int *bit, int pos)
/*@ With (a : list Z) (bit_l : list Z) (n : Z)
    Require
      1 <= n && n <= INT_MAX &&
      0 <= pos && pos <= n &&
      FenwickRep(a, bit_l, n) &&
      FenwickIntervalsIntSafe(a, n) &&
      IntArray::full(bit, n + 1, bit_l)
    Ensure
      __return == FenwickPrefixSum(a, pos) &&
      IntArray::full(bit, n + 1, bit_l)
 */
{
  int sum = 0;

  /*@ Inv Assert
      bit == bit@pre &&
      1 <= n && n <= INT_MAX &&
      0 <= pos && pos <= pos@pre && pos@pre <= n &&
      INT_MIN <= sum && sum <= INT_MAX &&
      FenwickRep(a, bit_l, n) &&
      FenwickIntervalsIntSafe(a, n) &&
      FenwickQueryState(a, pos@pre, pos, sum) &&
      IntArray::full(bit@pre, n + 1, bit_l)
   */
  while (pos > 0) {
    sum += bit[pos];
    pos -= lowbit(pos);
  }

  return sum;
}
