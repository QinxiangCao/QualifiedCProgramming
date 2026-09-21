



/*@ Extern Coq
      (LNDSLength : list Z -> Z -> Prop)
      (LNDTailsRepresentation : list Z -> Z -> Prop)
      (LNDTailsRealizability : list Z -> Z -> list Z -> Z -> Prop)
      (LNDSOptimalLength : list Z -> Z -> Z -> Prop)
      (LNDTailsMinimality : list Z -> Z -> list Z -> Z -> Prop)
      (UpperBoundPartition : list Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence.longest_nondecreasing_subsequence_lib */

int lengthOfLNDS(int *nums, int numsSize)
/*@ With (l : list Z)
    Require
      0 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      IntArray::full(nums, numsSize, l)
    Ensure
      LNDSLength(l, __return) &&
      IntArray::full(nums, numsSize, l)
 */
{
  int tails[100000];
  /*@ Inv Assert
      exists initialized,
      nums == nums@pre && numsSize == numsSize@pre &&
      0 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= fill && fill <= numsSize@pre &&
      Zlength(initialized) == fill &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::seg(tails, 0, fill, initialized) *
      IntArray::undef_seg(tails, fill, 100000)
   */
  for (int fill = 0; fill < numsSize; ++fill) {
    tails[fill] = 0;
  }

  int len = 0;
  /*@ Inv Assert
      exists tails_cur,
      nums == nums@pre && numsSize == numsSize@pre &&
      0 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      Zlength(tails_cur) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      0 <= len && len <= i &&
      LNDTailsRepresentation(sublist(0, len, tails_cur), len) &&
      LNDTailsRealizability(l, i, sublist(0, len, tails_cur), len) &&
      LNDSOptimalLength(l, i, len) &&
      LNDTailsMinimality(l, i, sublist(0, len, tails_cur), len) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::full(tails, numsSize@pre, tails_cur) *
      IntArray::undef_seg(tails, numsSize@pre, 100000)
   */
  for (int i = 0; i < numsSize; ++i) {
    int x = nums[i];
    
    int left = 0;
    int right = len;
    /*@ Inv Assert
      exists tails_cur,
      nums == nums@pre && numsSize == numsSize@pre &&
      0 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      Zlength(tails_cur) == numsSize@pre &&
      0 <= i && i < numsSize@pre &&
      0 <= len && len <= i &&
      x == l[i] &&
      0 <= left && left <= right && right <= len &&
      LNDTailsRepresentation(sublist(0, len, tails_cur), len) &&
      LNDTailsRealizability(l, i, sublist(0, len, tails_cur), len) &&
      LNDSOptimalLength(l, i, len) &&
      LNDTailsMinimality(l, i, sublist(0, len, tails_cur), len) &&
      UpperBoundPartition(sublist(0, len, tails_cur), len, x, left, right) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::full(tails, numsSize@pre, tails_cur) *
      IntArray::undef_seg(tails, numsSize@pre, 100000)
     */
    while (left < right) {
      int mid = left + (right - left) / 2;
      /*@ Assert
        exists tails_cur,
        nums == nums@pre && numsSize == numsSize@pre &&
        0 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        Zlength(tails_cur) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        0 <= len && len <= i &&
        x == l[i] &&
        0 <= left && left < right && right <= len &&
        left <= mid && mid < right &&
        LNDTailsRepresentation(sublist(0, len, tails_cur), len) &&
        LNDTailsRealizability(l, i, sublist(0, len, tails_cur), len) &&
        LNDSOptimalLength(l, i, len) &&
        LNDTailsMinimality(l, i, sublist(0, len, tails_cur), len) &&
        UpperBoundPartition(sublist(0, len, tails_cur), len, x, left, right) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::full(tails, numsSize@pre, tails_cur) *
        IntArray::undef_seg(tails, numsSize@pre, 100000)
       */
      if (tails[mid] <= x) {
        left = mid + 1;
      } else {
        right = mid;
      }
    }

    tails[left] = x;
    /*@ Assert
      exists tails_old,
      nums == nums@pre && numsSize == numsSize@pre &&
      0 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      Zlength(tails_old) == numsSize@pre &&
      0 <= i && i < numsSize@pre &&
      0 <= len && len <= i &&
      x == l[i] &&
      0 <= left && left <= len &&
      right == left &&
      LNDTailsRepresentation(sublist(0, len, tails_old), len) &&
      LNDTailsRealizability(l, i, sublist(0, len, tails_old), len) &&
      LNDSOptimalLength(l, i, len) &&
      LNDTailsMinimality(l, i, sublist(0, len, tails_old), len) &&
      UpperBoundPartition(sublist(0, len, tails_old), len, x, left, left) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::full(tails, numsSize@pre,
        app(sublist(0, left, tails_old),
            cons(x, sublist(left + 1, numsSize@pre, tails_old)))) *
      IntArray::undef_seg(tails, numsSize@pre, 100000)
     */
    if (left == len) {
      len = len + 1;
    }
    /*@ Assert
      exists tails_cur,
      nums == nums@pre && numsSize == numsSize@pre &&
      0 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      Zlength(tails_cur) == numsSize@pre &&
      0 <= i && i < numsSize@pre &&
      0 <= len && len <= i + 1 &&
      x == l[i] &&
      0 <= left && left <= len &&
      right == left &&
      LNDTailsRepresentation(sublist(0, len, tails_cur), len) &&
      LNDTailsRealizability(l, i + 1, sublist(0, len, tails_cur), len) &&
      LNDSOptimalLength(l, i + 1, len) &&
      LNDTailsMinimality(l, i + 1, sublist(0, len, tails_cur), len) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::full(tails, numsSize@pre, tails_cur) *
      IntArray::undef_seg(tails, numsSize@pre, 100000)
     */
  }
  /*@ Assert
      nums == nums@pre && numsSize == numsSize@pre &&
      LNDSLength(l, len) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::undef_full(tails, 100000)
   */
  return len;
}
