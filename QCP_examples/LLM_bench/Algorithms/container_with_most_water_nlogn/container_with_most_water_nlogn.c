/*@ Extern Coq
      (MaximumContainerArea : list Z -> Z -> Prop)
      (WorkspacePrefixNLogN : list Z -> list Z -> list Z -> Z -> Prop)
      (HeightIndexRangeDescendingNLogN : list Z -> Z -> Z -> Prop)
      (HeightIndexRangeSortResultNLogN : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (MergePrefixStateNLogN : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (HeightIndexRangeMergeResultNLogN : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (CopyHeightIndexPrefixNLogN : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (SortedHeightIndexWorkspaceNLogN : list Z -> list Z -> list Z -> Prop)
      (ProcessedIndexEndpointsNLogN : list Z -> Z -> Z -> Z -> Prop)
      (ProcessedContainerMaximumNLogN : list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_lib */

void mergeHeightIndexRunsNLogN(
    int *sourceHeight, int *sourceIndex,
    int *destinationHeight, int *destinationIndex,
    int count, int left, int middle, int right)
/*@ With source_h source_i dest0_h dest0_i
    Require
      Zlength(source_h) == count && Zlength(source_i) == count &&
      Zlength(dest0_h) == count && Zlength(dest0_i) == count &&
      0 <= left && left <= middle && middle <= right && right <= count &&
      HeightIndexRangeDescendingNLogN(source_h, left, middle) &&
      HeightIndexRangeDescendingNLogN(source_h, middle, right) &&
      IntArray::full(sourceHeight, count, source_h) *
      IntArray::full(sourceIndex, count, source_i) *
      IntArray::full(destinationHeight, count, dest0_h) *
      IntArray::full(destinationIndex, count, dest0_i)
    Ensure
      exists dest_h dest_i,
      HeightIndexRangeMergeResultNLogN(
        source_h, source_i, dest0_h, dest0_i, dest_h, dest_i,
        left, middle, right) &&
      IntArray::full(sourceHeight, count, source_h) *
      IntArray::full(sourceIndex, count, source_i) *
      IntArray::full(destinationHeight, count, dest_h) *
      IntArray::full(destinationIndex, count, dest_i)
 */
{
    int i = left;
    int j = middle;
    int output = left;

    /*@ Inv Assert
      exists dest_h dest_i,
      sourceHeight == sourceHeight@pre && sourceIndex == sourceIndex@pre &&
      destinationHeight == destinationHeight@pre &&
      destinationIndex == destinationIndex@pre &&
      count == count@pre && left == left@pre &&
      middle == middle@pre && right == right@pre &&
      Zlength(source_h) == count &&
      Zlength(source_i) == Zlength(source_h) &&
      Zlength(dest0_h) == count && Zlength(dest0_i) == count &&
      Zlength(dest_h) == Zlength(dest0_h) &&
      Zlength(dest_i) == Zlength(dest0_i) &&
      0 <= left && left <= i && i <= middle &&
      middle <= j && j <= right && right <= count &&
      output == left + (i - left) + (j - middle) &&
      left <= output && output <= right &&
      MergePrefixStateNLogN(
        source_h, source_i, dest0_h, dest0_i, dest_h, dest_i,
        left, middle, right, i, j, output) &&
      IntArray::full(sourceHeight, count, source_h) *
      IntArray::full(sourceIndex, count, source_i) *
      IntArray::full(destinationHeight, count, dest_h) *
      IntArray::full(destinationIndex, count, dest_i)
     */
    while (i < middle && j < right) {
        if (sourceHeight[i] >= sourceHeight[j]) {
            destinationHeight[output] = sourceHeight[i];
            destinationIndex[output] = sourceIndex[i];
            i++;
        } else {
            destinationHeight[output] = sourceHeight[j];
            destinationIndex[output] = sourceIndex[j];
            j++;
        }
        output++;
    }

    /*@ Inv Assert
      exists dest_h dest_i,
      sourceHeight == sourceHeight@pre && sourceIndex == sourceIndex@pre &&
      destinationHeight == destinationHeight@pre &&
      destinationIndex == destinationIndex@pre &&
      count == count@pre && left == left@pre &&
      middle == middle@pre && right == right@pre &&
      Zlength(source_h) == count &&
      Zlength(source_i) == Zlength(source_h) &&
      Zlength(dest0_h) == count && Zlength(dest0_i) == count &&
      Zlength(dest_h) == Zlength(dest0_h) &&
      Zlength(dest_i) == Zlength(dest0_i) &&
      (i == middle || j == right) &&
      0 <= left && left <= i && i <= middle &&
      middle <= j && j <= right && right <= count &&
      output == left + (i - left) + (j - middle) &&
      left <= output && output <= right &&
      MergePrefixStateNLogN(
        source_h, source_i, dest0_h, dest0_i, dest_h, dest_i,
        left, middle, right, i, j, output) &&
      IntArray::full(sourceHeight, count, source_h) *
      IntArray::full(sourceIndex, count, source_i) *
      IntArray::full(destinationHeight, count, dest_h) *
      IntArray::full(destinationIndex, count, dest_i)
     */
    while (i < middle) {
        destinationHeight[output] = sourceHeight[i];
        destinationIndex[output] = sourceIndex[i];
        i++;
        output++;
    }

    /*@ Inv Assert
      exists dest_h dest_i,
      sourceHeight == sourceHeight@pre && sourceIndex == sourceIndex@pre &&
      destinationHeight == destinationHeight@pre &&
      destinationIndex == destinationIndex@pre &&
      count == count@pre && left == left@pre &&
      middle == middle@pre && right == right@pre &&
      Zlength(source_h) == count &&
      Zlength(source_i) == Zlength(source_h) &&
      Zlength(dest0_h) == count && Zlength(dest0_i) == count &&
      Zlength(dest_h) == Zlength(dest0_h) &&
      Zlength(dest_i) == Zlength(dest0_i) &&
      i == middle &&
      0 <= left && left <= i && i <= middle &&
      middle <= j && j <= right && right <= count &&
      output == left + (i - left) + (j - middle) &&
      left <= output && output <= right &&
      MergePrefixStateNLogN(
        source_h, source_i, dest0_h, dest0_i, dest_h, dest_i,
        left, middle, right, i, j, output) &&
      IntArray::full(sourceHeight, count, source_h) *
      IntArray::full(sourceIndex, count, source_i) *
      IntArray::full(destinationHeight, count, dest_h) *
      IntArray::full(destinationIndex, count, dest_i)
     */
    while (j < right) {
        destinationHeight[output] = sourceHeight[j];
        destinationIndex[output] = sourceIndex[j];
        j++;
        output++;
    }
}

void sortHeightIndexRangeNLogN(
    int *workHeight, int *workIndex,
    int *bufferHeight, int *bufferIndex,
    int count, int left, int right)
/*@ With work0_h work0_i buffer0_h buffer0_i
    Require
      Zlength(work0_h) == count && Zlength(work0_i) == count &&
      Zlength(buffer0_h) == count && Zlength(buffer0_i) == count &&
      0 <= left && left <= right && right <= count && count <= 100000 &&
      IntArray::full(workHeight, count, work0_h) *
      IntArray::full(workIndex, count, work0_i) *
      IntArray::full(bufferHeight, count, buffer0_h) *
      IntArray::full(bufferIndex, count, buffer0_i)
    Ensure
      exists work_h work_i buffer_h buffer_i,
      HeightIndexRangeSortResultNLogN(
        work0_h, work0_i, work_h, work_i, left, right) &&
      IntArray::full(workHeight, count, work_h) *
      IntArray::full(workIndex, count, work_i) *
      IntArray::full(bufferHeight, count, buffer_h) *
      IntArray::full(bufferIndex, count, buffer_i)
 */
{
    if (right - left <= 1) {
        return;
    }

    int middle = left + (right - left) / 2;
    sortHeightIndexRangeNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        count, left, middle);
    sortHeightIndexRangeNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        count, middle, right);

    /*@ Assert
      exists work_mid_h work_mid_i work_h work_i buffer_h buffer_i,
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      count == count@pre && count <= 100000 &&
      left == left@pre && right == right@pre &&
      left < middle && middle < right &&
      Zlength(work_mid_h) == count && Zlength(work_mid_i) == count &&
      Zlength(work_h) == count && Zlength(work_i) == count &&
      Zlength(buffer_h) == count && Zlength(buffer_i) == count &&
      HeightIndexRangeSortResultNLogN(
        work0_h, work0_i, work_mid_h, work_mid_i, left, middle) &&
      HeightIndexRangeSortResultNLogN(
        work_mid_h, work_mid_i, work_h, work_i, middle, right) &&
      HeightIndexRangeDescendingNLogN(work_h, left, middle) &&
      HeightIndexRangeDescendingNLogN(work_h, middle, right) &&
      IntArray::full(workHeight, count, work_h) *
      IntArray::full(workIndex, count, work_i) *
      IntArray::full(bufferHeight, count, buffer_h) *
      IntArray::full(bufferIndex, count, buffer_i)
     */
    mergeHeightIndexRunsNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        count, left, middle, right);

    /*@ Assert
      exists work_mid_h work_mid_i work_h work_i
             buffer0_h buffer0_i buffer_h buffer_i,
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      count == count@pre && count <= 100000 &&
      left == left@pre && right == right@pre &&
      left < middle && middle < right &&
      Zlength(work_mid_h) == count && Zlength(work_mid_i) == count &&
      Zlength(work_h) == count && Zlength(work_i) == count &&
      Zlength(buffer_h) == count && Zlength(buffer_i) == count &&
      0 <= left && right <= count &&
      HeightIndexRangeSortResultNLogN(
        work0_h, work0_i, work_mid_h, work_mid_i, left, middle) &&
      HeightIndexRangeSortResultNLogN(
        work_mid_h, work_mid_i, work_h, work_i, middle, right) &&
      HeightIndexRangeMergeResultNLogN(
        work_h, work_i, buffer0_h, buffer0_i, buffer_h, buffer_i,
        left, middle, right) &&
      IntArray::full(workHeight, count, work_h) *
      IntArray::full(workIndex, count, work_i) *
      IntArray::full(bufferHeight, count, buffer_h) *
      IntArray::full(bufferIndex, count, buffer_i)
     */

    /*@ Inv Assert
      exists work_mid_h work_mid_i work_h work_i
             buffer0_h buffer0_i buffer_h buffer_i work_h1 work_i1,
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      count == count@pre && count <= 100000 &&
      left == left@pre && right == right@pre &&
      left < middle && middle < right &&
      Zlength(work_mid_h) == count && Zlength(work_mid_i) == count &&
      Zlength(work_h) == count && Zlength(work_i) == count &&
      Zlength(work_h1) == count && Zlength(work_i1) == count &&
      Zlength(buffer_h) == count && Zlength(buffer_i) == count &&
      0 <= left && left <= k && k <= right && right <= count &&
      HeightIndexRangeSortResultNLogN(
        work0_h, work0_i, work_mid_h, work_mid_i, left, middle) &&
      HeightIndexRangeSortResultNLogN(
        work_mid_h, work_mid_i, work_h, work_i, middle, right) &&
      HeightIndexRangeMergeResultNLogN(
        work_h, work_i, buffer0_h, buffer0_i, buffer_h, buffer_i,
        left, middle, right) &&
      CopyHeightIndexPrefixNLogN(
        buffer_h, buffer_i, work_h, work_i, work_h1, work_i1,
        left, right, k) &&
      IntArray::full(workHeight, count, work_h1) *
      IntArray::full(workIndex, count, work_i1) *
      IntArray::full(bufferHeight, count, buffer_h) *
      IntArray::full(bufferIndex, count, buffer_i)
     */
    for (int k = left; k < right; ++k) {
        workHeight[k] = bufferHeight[k];
        workIndex[k] = bufferIndex[k];
    }
}

int maxAreaNLogN(
    const int *height, int heightSize,
    int *workHeight, int *workIndex,
    int *bufferHeight, int *bufferIndex)
/*@ With (l : list Z)
    Require
      2 <= heightSize && heightSize <= 100000 &&
      Zlength(l) == heightSize &&
      (forall (k : Z),
        (0 <= k && k < heightSize) =>
        (0 <= l[k] && l[k] <= 10000)) &&
      IntArray::full(height, heightSize, l) *
      IntArray::undef_full(workHeight, heightSize) *
      IntArray::undef_full(workIndex, heightSize) *
      IntArray::undef_full(bufferHeight, heightSize) *
      IntArray::undef_full(bufferIndex, heightSize)
    Ensure
      exists sorted_h sorted_i buffer_h buffer_i,
      MaximumContainerArea(l, __return) &&
      0 <= __return && __return <= 999990000 &&
      SortedHeightIndexWorkspaceNLogN(l, sorted_h, sorted_i) &&
      IntArray::full(height, heightSize, l) *
      IntArray::full(workHeight, heightSize, sorted_h) *
      IntArray::full(workIndex, heightSize, sorted_i) *
      IntArray::full(bufferHeight, heightSize, buffer_h) *
      IntArray::full(bufferIndex, heightSize, buffer_i)
 */
{
    /*@ Inv Assert
      exists work_h work_i buffer_h buffer_i,
      height == height@pre && heightSize == heightSize@pre &&
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      2 <= heightSize@pre && heightSize@pre <= 100000 &&
      Zlength(l) == heightSize@pre &&
      0 <= k && k <= heightSize@pre &&
      Zlength(work_h) == k && Zlength(work_i) == k &&
      Zlength(buffer_h) == k && Zlength(buffer_i) == k &&
      WorkspacePrefixNLogN(l, work_h, work_i, k) &&
      WorkspacePrefixNLogN(l, buffer_h, buffer_i, k) &&
      (forall (p : Z),
        (0 <= p && p < heightSize@pre) =>
        (0 <= l[p] && l[p] <= 10000)) &&
      IntArray::full(height, heightSize@pre, l) *
      IntArray::full(workHeight, k, work_h) *
      IntArray::undef_seg(workHeight, k, heightSize@pre) *
      IntArray::full(workIndex, k, work_i) *
      IntArray::undef_seg(workIndex, k, heightSize@pre) *
      IntArray::full(bufferHeight, k, buffer_h) *
      IntArray::undef_seg(bufferHeight, k, heightSize@pre) *
      IntArray::full(bufferIndex, k, buffer_i) *
      IntArray::undef_seg(bufferIndex, k, heightSize@pre)
     */
    for (int k = 0; k < heightSize; ++k) {
        int h = height[k];
        workHeight[k] = h;
        workIndex[k] = k;
        bufferHeight[k] = h;
        bufferIndex[k] = k;
    }

    /*@ Assert
      exists work0_h work0_i buffer0_h buffer0_i,
      height == height@pre && heightSize == heightSize@pre &&
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      2 <= heightSize@pre && heightSize@pre <= 100000 &&
      Zlength(l) == heightSize@pre &&
      Zlength(work0_h) == heightSize@pre &&
      Zlength(work0_i) == heightSize@pre &&
      Zlength(buffer0_h) == heightSize@pre &&
      Zlength(buffer0_i) == heightSize@pre &&
      WorkspacePrefixNLogN(l, work0_h, work0_i, heightSize@pre) &&
      WorkspacePrefixNLogN(l, buffer0_h, buffer0_i, heightSize@pre) &&
      (forall (p : Z),
        (0 <= p && p < heightSize@pre) =>
        (0 <= l[p] && l[p] <= 10000)) &&
      IntArray::full(height, heightSize@pre, l) *
      IntArray::full(workHeight, heightSize@pre, work0_h) *
      IntArray::full(workIndex, heightSize@pre, work0_i) *
      IntArray::full(bufferHeight, heightSize@pre, buffer0_h) *
      IntArray::full(bufferIndex, heightSize@pre, buffer0_i)
     */

    sortHeightIndexRangeNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        heightSize, 0, heightSize);

    /*@ Assert
      exists sorted_h sorted_i buffer_h buffer_i,
      height == height@pre && heightSize == heightSize@pre &&
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      2 <= heightSize@pre && heightSize@pre <= 100000 &&
      Zlength(l) == heightSize@pre &&
      SortedHeightIndexWorkspaceNLogN(l, sorted_h, sorted_i) &&
      (forall (p : Z),
        (0 <= p && p < heightSize@pre) =>
        (0 <= l[p] && l[p] <= 10000)) &&
      IntArray::full(height, heightSize@pre, l) *
      IntArray::full(workHeight, heightSize@pre, sorted_h) *
      IntArray::full(workIndex, heightSize@pre, sorted_i) *
      IntArray::full(bufferHeight, heightSize@pre, buffer_h) *
      IntArray::full(bufferIndex, heightSize@pre, buffer_i)
     */

    int minimumIndex = workIndex[0];
    int maximumIndex = workIndex[0];
    int maximumArea = 0;

    /*@ Inv Assert
      exists sorted_h sorted_i buffer_h buffer_i,
      height == height@pre && heightSize == heightSize@pre &&
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      2 <= heightSize@pre && heightSize@pre <= 100000 &&
      Zlength(l) == heightSize@pre &&
      1 <= k && k <= heightSize@pre &&
      0 <= minimumIndex && minimumIndex <= maximumIndex &&
      maximumIndex < heightSize@pre &&
      0 <= maximumArea && maximumArea <= 999990000 &&
      SortedHeightIndexWorkspaceNLogN(l, sorted_h, sorted_i) &&
      ProcessedIndexEndpointsNLogN(
        sorted_i, k, minimumIndex, maximumIndex) &&
      ProcessedContainerMaximumNLogN(l, sorted_i, k, maximumArea) &&
      (forall (p : Z),
        (0 <= p && p < heightSize@pre) =>
        (0 <= l[p] && l[p] <= 10000)) &&
      IntArray::full(height, heightSize@pre, l) *
      IntArray::full(workHeight, heightSize@pre, sorted_h) *
      IntArray::full(workIndex, heightSize@pre, sorted_i) *
      IntArray::full(bufferHeight, heightSize@pre, buffer_h) *
      IntArray::full(bufferIndex, heightSize@pre, buffer_i)
     */
    for (int k = 1; k < heightSize; ++k) {
        int index = workIndex[k];
        int currentHeight = workHeight[k];
        int distanceToMinimum = index - minimumIndex;
        int distanceToMaximum = maximumIndex - index;

        if (distanceToMinimum < 0) {
            distanceToMinimum = -distanceToMinimum;
        }
        if (distanceToMaximum < 0) {
            distanceToMaximum = -distanceToMaximum;
        }

        int width;
        if (distanceToMinimum > distanceToMaximum) {
            width = distanceToMinimum;
        } else {
            width = distanceToMaximum;
        }

        /*@ Branch join all with Assert
          exists sorted_h sorted_i buffer_h buffer_i,
          height == height@pre && heightSize == heightSize@pre &&
          workHeight == workHeight@pre && workIndex == workIndex@pre &&
          bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
          2 <= heightSize@pre && heightSize@pre <= 100000 &&
          Zlength(l) == heightSize@pre &&
          1 <= k && k < heightSize@pre &&
          index == sorted_i[k] && currentHeight == sorted_h[k] &&
          currentHeight == l[index] &&
          0 <= index && index < heightSize@pre &&
          0 <= minimumIndex && minimumIndex <= maximumIndex &&
          maximumIndex < heightSize@pre &&
          0 <= currentHeight && currentHeight <= 10000 &&
          0 <= distanceToMinimum && distanceToMinimum <= 99999 &&
          0 <= distanceToMaximum && distanceToMaximum <= 99999 &&
          (distanceToMinimum == index - minimumIndex ||
           distanceToMinimum == minimumIndex - index) &&
          (distanceToMaximum == maximumIndex - index ||
           distanceToMaximum == index - maximumIndex) &&
          distanceToMinimum <= width && distanceToMaximum <= width &&
          (width == distanceToMinimum || width == distanceToMaximum) &&
          0 <= width && width <= 99999 &&
          0 <= maximumArea && maximumArea <= 999990000 &&
          SortedHeightIndexWorkspaceNLogN(l, sorted_h, sorted_i) &&
          ProcessedIndexEndpointsNLogN(
            sorted_i, k, minimumIndex, maximumIndex) &&
          ProcessedContainerMaximumNLogN(l, sorted_i, k, maximumArea) &&
          (forall (p : Z),
            (0 <= p && p < heightSize@pre) =>
            (0 <= l[p] && l[p] <= 10000)) &&
          IntArray::full(height, heightSize@pre, l) *
          IntArray::full(workHeight, heightSize@pre, sorted_h) *
          IntArray::full(workIndex, heightSize@pre, sorted_i) *
          IntArray::full(bufferHeight, heightSize@pre, buffer_h) *
          IntArray::full(bufferIndex, heightSize@pre, buffer_i)
         */

        int area = width * currentHeight;
        if (area > maximumArea) {
            maximumArea = area;
        }

        if (index < minimumIndex) {
            /*@ distanceToMaximum == width by local */
            minimumIndex = index;
        }
        if (index > maximumIndex) {
            /*@ distanceToMinimum == width by local */
            maximumIndex = index;
        }
    }

    /*@ Assert
      exists sorted_h sorted_i buffer_h buffer_i,
      height == height@pre && heightSize == heightSize@pre &&
      workHeight == workHeight@pre && workIndex == workIndex@pre &&
      bufferHeight == bufferHeight@pre && bufferIndex == bufferIndex@pre &&
      MaximumContainerArea(l, maximumArea) &&
      0 <= maximumArea && maximumArea <= 999990000 &&
      0 <= minimumIndex && minimumIndex < heightSize &&
      0 <= maximumIndex && maximumIndex < heightSize &&
      minimumIndex <= maximumIndex &&
      SortedHeightIndexWorkspaceNLogN(l, sorted_h, sorted_i) &&
      IntArray::full(height, heightSize, l) *
      IntArray::full(workHeight, heightSize, sorted_h) *
      IntArray::full(workIndex, heightSize, sorted_i) *
      IntArray::full(bufferHeight, heightSize, buffer_h) *
      IntArray::full(bufferIndex, heightSize, buffer_i)
     */
    return maximumArea;
}
