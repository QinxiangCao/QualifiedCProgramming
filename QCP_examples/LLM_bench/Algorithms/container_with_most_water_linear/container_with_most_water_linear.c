#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (LinearContainerHeight : list Z -> Z -> Z -> Z)
      (LinearContainerArea : list Z -> Z -> Z -> Z)
      (MaximumContainerArea : list Z -> Z -> Prop)
      (LinearContainerTwoPointerInvariant : list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_lib */

/*
 * Linear-time two-pointer implementation of Container With Most Water.
 * The input array is only read and is never modified.
 */
int maxAreaLinear(const int *height, int heightSize)
/*@ With (l : list Z)
    Require
      2 <= heightSize && heightSize <= 100000 &&
      height != 0 &&
      Zlength(l) == heightSize &&
      IntArray::full(height, heightSize, l) &&
      (forall (k : Z),
        (0 <= k && k < heightSize) =>
        (0 <= l[k] && l[k] <= 10000))
    Ensure
      MaximumContainerArea(l, __return) &&
      0 <= __return && __return <= 999990000 &&
      IntArray::full(height, heightSize, l)
 */
{
    int left;
    int right;
    int maximumArea;

    if (height == 0 || heightSize < 2) {
        return 0;
    }

    left = 0;
    right = heightSize - 1;
    maximumArea = 0;

    /*@ Inv Assert
      height == height@pre && heightSize == heightSize@pre &&
      2 <= heightSize@pre && heightSize@pre <= 100000 &&
      Zlength(l) == heightSize@pre &&
      0 <= left && left <= right && right < heightSize@pre &&
      0 <= maximumArea && maximumArea <= 999990000 &&
      LinearContainerTwoPointerInvariant(l, left, right, maximumArea) &&
      IntArray::full(height, heightSize@pre, l) &&
      (forall (k : Z),
        (0 <= k && k < heightSize@pre) =>
        (0 <= l[k] && l[k] <= 10000))
     */
    while (left < right) {
        int width = right - left;
        int shorterHeight;
        int area;

        if (height[left] < height[right]) {
            shorterHeight = height[left];
        } else {
            shorterHeight = height[right];
        }

        area = width * shorterHeight;
        if (area > maximumArea) {
            maximumArea = area;
        }

        /*@ Assert
          height == height@pre && heightSize == heightSize@pre &&
          2 <= heightSize@pre && heightSize@pre <= 100000 &&
          Zlength(l) == heightSize@pre &&
          0 <= left && left < right && right < heightSize@pre &&
          width == right - left &&
          1 <= width && width <= 99999 &&
          shorterHeight == LinearContainerHeight(l, left, right) &&
          0 <= shorterHeight && shorterHeight <= 10000 &&
          area == LinearContainerArea(l, left, right) &&
          0 <= area && area <= maximumArea &&
          0 <= maximumArea && maximumArea <= 999990000 &&
          LinearContainerTwoPointerInvariant(l, left, right, maximumArea) &&
          IntArray::full(height, heightSize@pre, l) &&
          (forall (k : Z),
            (0 <= k && k < heightSize@pre) =>
            (0 <= l[k] && l[k] <= 10000))
         */

        /*
         * Moving the taller side cannot improve the current shorter side:
         * the width becomes smaller while the usable height cannot exceed
         * the shorter endpoint.  Therefore discard the shorter endpoint.
         */
        if (height[left] < height[right]) {
            ++left;
        } else {
            --right;
        }
    }

    /*@ Assert
      height == height@pre && heightSize == heightSize@pre &&
      2 <= heightSize@pre && heightSize@pre <= 100000 &&
      Zlength(l) == heightSize@pre &&
      0 <= left && left == right && right < heightSize@pre &&
      LinearContainerTwoPointerInvariant(l, left, right, maximumArea) &&
      MaximumContainerArea(l, maximumArea) &&
      0 <= maximumArea && maximumArea <= 999990000 &&
      IntArray::full(height, heightSize@pre, l)
     */
    return maximumArea;
}
