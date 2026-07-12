



/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (strict_lowerbound : Z -> list Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.sortArray_lib */

int* sortArray(int* nums, int numsSize, int* returnSize) 
/*@ With (l: list Z)
    Require Zlength(l) == numsSize && 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l) * undef_data_at(returnSize)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && Zlength(l1) == numsSize && IntArray::full(__return, numsSize, l1) && *returnSize == numsSize
*/
{
    *returnSize = numsSize;
    /*@ Inv Assert
        exists l1 l2 l0,
            nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
            1 <= numsSize && numsSize <= 50000 &&
            l == app(l1, l2) &&
            i == Zlength(l1) &&
            1 <= i && i <= numsSize &&
            Permutation(l1, l0) && increasing(l0) &&
            *returnSize == numsSize@pre &&
            IntArray::seg(nums, 0, i, l0) *
            IntArray::seg(nums, i, numsSize, l2)
    */
    for (int i = 1; i < numsSize; ++i) {
        int key = nums[i];
        int j = i - 1;
        /*@ Inv Assert
            exists l1 l2 l0 l3 l4,
                nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
                1 <= numsSize && numsSize <= 50000 &&
                l == app(l1, cons(key, l4)) &&
                i == Zlength(l1) &&
                1 <= i && i <= numsSize &&
                Permutation(l1, l0) && increasing(l0) &&
                l0 == app(l2, l3) &&
                j + 1 == Zlength(l2) && j + 1 <= i && 
                strict_lowerbound(key, l3) &&
                *returnSize == numsSize@pre &&
                IntArray::seg(nums, 0, j + 1, l2) *
                undef_data_at(nums + ((j + 1) * sizeof(int)), int) *
                IntArray::missing_i(nums, j + 1, j + 1, i + 1, cons(key, l3)) *
                IntArray::seg(nums, i + 1, numsSize, l4)
        */
        while (j >= 0 && nums[j] > key) {
            /*@ Assert exists l1 l2 l0 l3 l4 l5,
                    l2 == app(l5, cons(l2[j], nil)) &&
                    j == Zlength(l5) && j + 1 <= i &&
                    nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
                    1 <= numsSize && numsSize <= 50000 &&
                    l == app(l1, cons(key, l4)) &&
                    i == Zlength(l1) &&
                    1 <= i && i <= numsSize && 
                    Permutation(l1, l0) && increasing(l0) &&
                    l0 == app(l2, l3) &&
                    strict_lowerbound(key, l3) &&
                    0 <= j && l2[j] > key &&
                    *returnSize == numsSize@pre &&
                    IntArray::seg(nums, 0, j, l5) *
                    store(nums + (j * sizeof(int)), int, l2[j]) *
                        undef_data_at(nums + ((j + 1) * sizeof(int)), int) *
                    IntArray::missing_i(nums, j + 1, j + 1, i + 1, cons(key, l3)) *
                    IntArray::seg(nums, i + 1, numsSize, l4)
            */
            nums[j + 1] = nums[j];
                    /*@ Assert exists l1 l2 l0 l3 l4 l5,
                    l2 == app(l5, cons(l2[j], nil)) &&
                    j == Zlength(l5) && j + 1 <= i &&
                    nums == nums@pre && numsSize == numsSize@pre && returnSize == returnSize@pre &&
                    1 <= numsSize && numsSize <= 50000 &&
                    l == app(l1, cons(key, l4)) &&
                    i == Zlength(l1) &&
                    1 <= i && i <= numsSize &&
                    Permutation(l1, l0) && increasing(l0) &&
                    l0 == app(l2, l3) &&
                    strict_lowerbound(key, l3) &&
                    0 <= j && l2[j] > key &&
                    *returnSize == numsSize@pre &&
                    IntArray::seg(nums, 0, j, l5) *
                    undef_data_at(nums + (j * sizeof(int)), int) *
                    IntArray::missing_i(nums, j, j, i + 1, cons(key, cons(l2[j], l3))) *
                    IntArray::seg(nums, i + 1, numsSize, l4)
            */
            j--;
        }
        nums[j + 1] = key;
    }
    return nums;
}
