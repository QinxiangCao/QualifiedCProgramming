



/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (lowerbound : Z -> list Z -> Prop) */
/*@ Extern Coq (prefix_suffix_sorted : list Z -> list Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib */

int* sortArray(int* nums, int numsSize, int* returnSize) 
/*@ With (l: list Z)
    Require Zlength(l) == numsSize && 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l) * has_int_permission(returnSize)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && Zlength(l1) == numsSize && IntArray::full(__return, numsSize, l1) && *returnSize == numsSize
*/
{
    *returnSize = numsSize;
    /*@ Inv Assert
        exists l1 l2 l3,
            nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
            1 <= numsSize && numsSize <= 50000 &&
            l3 == app(l1, l2) &&
            numsSize == Zlength(l) &&
            i == Zlength(l1) &&
            0 <= i && i <= numsSize &&
            Permutation(l, l3) &&
            increasing(l1) &&
            prefix_suffix_sorted(l1, l2) &&
            *returnSize == numsSize@pre &&
            IntArray::full(nums, numsSize, l3)
    */
    for (int i = 0; i < numsSize; ++i) {
        /*@ Inv Assert
            exists l1 l2 l3 l4 key,
                nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
                1 <= numsSize && numsSize <= 50000 &&
                l3 == app(l1, app(cons(key, l2), l4)) &&
                numsSize == Zlength(l) &&
                i == Zlength(l1) &&
                0 <= i && i < numsSize &&
                j == Zlength(app(l1, cons(key, l2))) &&
                i + 1 <= j && j <= numsSize &&
                Permutation(l, l3) &&
                increasing(l1) &&
                prefix_suffix_sorted(l1, app(cons(key, l2), l4)) &&
                lowerbound(key, l2) &&
                *returnSize == numsSize@pre &&
                IntArray::full(nums, numsSize, l3)
        */
        for (int j = i + 1; j < numsSize; ++j) {
            if (nums[j] < nums[i]) {
                int tmp = nums[i];
                nums[i] = nums[j];
                nums[j] = tmp;
            }
        }
    }
    return nums;
}