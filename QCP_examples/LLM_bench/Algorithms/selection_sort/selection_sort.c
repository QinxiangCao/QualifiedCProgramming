



/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */

void sortArray(int* nums, int numsSize) 
/*@ With (l: list Z)
    Require 1 <= numsSize && numsSize <= 50000 && IntArray::full(nums, numsSize, l)
    Ensure exists l1, Permutation(l, l1) && increasing(l1) && IntArray::full(nums, numsSize, l1)
*/
{
    /*@ Inv Assert
        exists a,
            nums == nums@pre && numsSize == numsSize@pre &&
            1 <= numsSize && numsSize <= 50000 &&
            0 <= i && i <= numsSize &&
            Permutation(l, a) &&
            increasing(sublist(0, i, a)) &&
            (forall (p: Z) (q: Z),
                (0 <= p && p < i && i <= q && q < numsSize) =>
                (a[p] <= a[q])) &&
            IntArray::full(nums, numsSize, a)
        by array_length
    */
    for (int i = 0; i < numsSize; ++i) {
        /*@ Inv Assert
            exists a,
                nums == nums@pre && numsSize == numsSize@pre &&
                1 <= numsSize && numsSize <= 50000 &&
                0 <= i && i < numsSize &&
                i + 1 <= j && j <= numsSize &&
                Permutation(l, a) &&
                increasing(sublist(0, i, a)) &&
                (forall (p: Z) (q: Z),
                    (0 <= p && p < i && i <= q && q < numsSize) =>
                    (a[p] <= a[q])) &&
                (forall (q: Z),
                    (i <= q && q < j) =>
                    (a[i] <= a[q])) &&
                IntArray::full(nums, numsSize, a)
            by array_length
        */
        for (int j = i + 1; j < numsSize; ++j) {
            if (nums[j] < nums[i]) {
                int tmp = nums[i];
                nums[i] = nums[j];
                nums[j] = tmp;
            }
        }
    }
    return /*@ by array_length */;
}
