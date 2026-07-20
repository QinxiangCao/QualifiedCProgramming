



/*@ Extern Coq (IsMajorityElement : Z -> list Z -> Prop) */
/*@ Extern Coq (MajorityOnReduced : Z -> Z -> Z -> list Z -> Prop) */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_lib */

int majorityElement(int* nums, int numsSize)
/*@ With (l : list Z)
    Require exists x, IsMajorityElement(x,l) && 1 <= numsSize && numsSize <= 50000 && Zlength(l) == numsSize && IntArray::full(nums, numsSize, l)
    Ensure IsMajorityElement(__return, l) && IntArray::full(nums, numsSize, l)
*/
{
    int vote = 0;
    int candidate = 0;
    /*@ Inv Assert
        exists x l1 l2,
            nums == nums@pre && numsSize == numsSize@pre &&
            l == app(l1, l2) &&
            i == Zlength(l1) &&
            0 <= i && i <= numsSize &&
            1 <= numsSize && numsSize <= 50000 &&
            0 <= vote && vote <= i &&
            IsMajorityElement(x, l) &&
            MajorityOnReduced(x, candidate, vote, l2) &&
            IntArray::full(nums, numsSize, l)
    */
    for (int i = 0; i < numsSize; i++) {
        if (vote == 0) {
            candidate = nums[i];
        }
        vote += (nums[i] == candidate) ? 1 : -1;
    }
    return candidate;
}