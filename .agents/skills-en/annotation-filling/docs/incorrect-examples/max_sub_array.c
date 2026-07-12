#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
               (max_Z : Z -> Z -> Z)
               (max_suffix_sum : list Z -> Z)
               (max_subarray_sum : list Z -> Z)
               (kadane_safe : list Z -> Prop)
               (IntuitiveMaxSubArraySum : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.max_sub_array_lib */

int max(int a, int b)
/*@ Require emp
    Ensure __return == max_Z(a, b) && emp
*/
{
    return (a > b) ? a : b;
}

int max_sub_array(int *arr, int n)
/*@ With (l : list Z)
    Require 0 <= n && Zlength(l) == n && kadane_safe(l) && IntArray::full(arr, n, l)
    Ensure IntArray::full(arr, n, l) &&
           ((n == 0 && __return == 0) || (0 < n && IntuitiveMaxSubArraySum(l, __return)))
*/
{
    if (n == 0) {
        return 0;
    }

    int cur = arr[0];
    int res = arr[0];

    /*@ Inv Assert
          arr == arr@pre && n == n@pre &&
          0 < n@pre && Zlength(l) == n@pre && kadane_safe(l) &&
          1 <= i && i <= n@pre &&
          cur == max_suffix_sum(sublist(0, i, l)) &&
          res == max_subarray_sum(sublist(0, i, l)) &&
          IntArray::full(arr, n@pre, l)
    */
    for (int i = 1; i < n; i++) {
        /*@ Assert
              arr == arr@pre && n == n@pre &&
              0 < n@pre && Zlength(l) == n@pre && kadane_safe(l) &&
              1 <= i && i < n@pre &&
              INT_MIN <= cur + l[i] && cur + l[i] <= INT_MAX &&
              cur == max_suffix_sum(sublist(0, i, l)) &&
              res == max_subarray_sum(sublist(0, i, l)) &&
              IntArray::full(arr, n@pre, l)
        */
        cur = max(arr[i], cur + arr[i]);
        /*@ Assert
              arr == arr@pre && n == n@pre &&
              0 < n@pre && Zlength(l) == n@pre && kadane_safe(l) &&
              1 <= i && i < n@pre &&
              cur == max_suffix_sum(sublist(0, i + 1, l)) &&
              res == max_subarray_sum(sublist(0, i, l)) &&
              IntArray::full(arr, n@pre, l)
        */
        res = max(res, cur);
        /*@ Assert
              arr == arr@pre && n == n@pre &&
              0 < n@pre && Zlength(l) == n@pre && kadane_safe(l) &&
              1 <= i && i < n@pre &&
              cur == max_suffix_sum(sublist(0, i + 1, l)) &&
              res == max_subarray_sum(sublist(0, i + 1, l)) &&
              IntArray::full(arr, n@pre, l)
        */
    }
    /*@ Assert
          arr == arr@pre && n == n@pre &&
          0 < n@pre && Zlength(l) == n@pre && kadane_safe(l) &&
          cur == max_suffix_sum(l) &&
          res == max_subarray_sum(l) &&
          IntArray::full(arr, n@pre, l)
    */
    return res;
}
