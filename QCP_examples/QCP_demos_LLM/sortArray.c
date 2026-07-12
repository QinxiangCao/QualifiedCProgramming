



/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (strict_lowerbound : Z -> list Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sortArray_lib */

int* sortArray(int* nums, int numsSize, int* returnSize) 
/*@ With (l: list Z)
    Require Zlength(l) == numsSize && 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l) * has_int_permission(returnSize)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && Zlength(l1) == numsSize && IntArray::full(__return, numsSize, l1) && *returnSize == numsSize
*/
{
    *returnSize = numsSize;
    /*@ Inv Assert
        exists l1 l2 l0 l3,
            nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
            1 <= numsSize && numsSize <= 50000 &&
            l == app(l1, l2) &&
            l3 == app(l0, l2) &&
            numsSize == Zlength(l) && 
            i == Zlength(l1) &&
            1 <= i && i <= numsSize &&
            Permutation(l1, l0) && increasing(l0) &&
            *returnSize == numsSize@pre &&
            IntArray::full(nums, numsSize, l3)
    */
    for (int i = 1; i < numsSize; ++i) {
        int key = nums[i];
        int j = i - 1;
        /*@ Inv Assert
            exists l1 l2 l0 l3 l4 l5,
                nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
                1 <= numsSize && numsSize <= 50000 &&
                l == app(l1, cons(key, l4)) &&
                numsSize == Zlength(l) &&
                i == Zlength(l1) &&
                1 <= i && i < numsSize &&
                Permutation(l1, l0) && increasing(l0) &&
                l0 == app(l2, l3) &&
                l5 == app(app(l2, cons(Znth(j+1, l0, key), l3)), l4) &&
                0 <= j + 1 && j + 1 == Zlength(l2) && j + 1 <= i && j + 1 < numsSize &&
                strict_lowerbound(key, l3) &&
                *returnSize == numsSize@pre &&
                IntArray::full(nums, numsSize, l5)
        */
        while (j >= 0 && nums[j] > key) {
            nums[j + 1] = nums[j];
            j--;
        }
        nums[j + 1] = key;
    }
    return nums;
}
