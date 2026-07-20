



/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (prefix_suffix_sorted : list Z -> list Z -> Prop) */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_lib */

int* sortArray(int* nums, int numsSize, int* returnSize) 
/*@ With (l: list Z)
    Require Zlength(l) == numsSize && 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l) * has_int_permission(returnSize)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && Zlength(l1) == numsSize && IntArray::full(__return, numsSize, l1) && *returnSize == numsSize
*/
{
    *returnSize = numsSize;
    if (numsSize <= 1) {
        return nums;
    }
    /*@ Inv Assert
        exists l1 l2 l3,
            nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
            1 <= numsSize && numsSize <= 50000 &&
            l3 == app(l1, l2) &&
            numsSize == Zlength(l) &&
            i == Zlength(l2) &&
            0 <= i && i < numsSize &&
            1 <= Zlength(l1) &&
            Permutation(l, l3) &&
            increasing(l2) &&
            prefix_suffix_sorted(l1, l2) &&
            *returnSize == numsSize@pre &&
            IntArray::full(nums, numsSize, l3)
    */
    for (int i = 0; i < numsSize - 1; ++i) {
        /*@ Inv Assert
            exists l1 l2 l3 l4 key,
                nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
                1 <= numsSize && numsSize <= 50000 &&
                l3 == app(app(l1, cons(key, l2)), l4) &&
                numsSize == Zlength(l) &&
                i == Zlength(l4) &&
                0 <= i && i < numsSize &&
                i < numsSize - 1 &&
                j == Zlength(l1) &&
                0 <= j && j + 1 <= numsSize - i &&
                numsSize - i == Zlength(app(l1, cons(key, l2))) &&
                Permutation(l, l3) &&
                increasing(l4) &&
                prefix_suffix_sorted(app(l1, cons(key, l2)), l4) &&
                prefix_suffix_sorted(l1, cons(key, nil)) &&
                *returnSize == numsSize@pre &&
                IntArray::full(nums, numsSize, l3)
        */
        for (int j = 0; j + 1 < numsSize - i; ++j) {
            if (nums[j] > nums[j + 1]) {
                int tmp = nums[j];
                nums[j] = nums[j + 1];
                nums[j + 1] = tmp;
            }
        }
    }
    return nums;
}