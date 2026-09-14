/*
 * LeetCode 435: Non-overlapping Intervals.
 *
 * The two arrays st and ed represent the interval records in parallel:
 * interval i is [st[i], ed[i]].  Quicksort always swaps both fields of a
 * record, then the earliest-finish-time scan computes a maximum-cardinality
 * compatible subset.  Therefore intervalsSize - kept is the minimum number
 * of removals.
 */

/*@ Extern Coq (interval :: *) */
/*@ Extern Coq
      (PairIntervals : list Z -> list Z -> list interval -> Prop)
      (IntervalBounds : list interval -> Prop)
      (IntervalPermutation : list interval -> list interval -> Prop)
      (IntervalSwappedAt : list interval -> list interval -> Z -> Z -> Prop)
      (IntervalSameOutsideRange : list interval -> list interval -> Z -> Z -> Prop)
      (IntervalPartitionedAt : list interval -> Z -> Z -> Z -> Prop)
      (IntervalsEndSortedRange : list interval -> Z -> Z -> Prop)
      (IntervalsEndSorted : list interval -> Prop)
      (MinimumRemovals : list interval -> Z -> Prop)
      (LomutoScanState : list interval -> list interval -> Z -> Z -> Z -> Z -> Z -> Prop)
      (GreedyPrefixState : list interval -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_lib */

void swap_intervals(int *st, int *ed, int i, int j)
/*@ With n st_l ed_l ps
    Require
      0 <= i && i < n && 0 <= j && j < n &&
      PairIntervals(st_l, ed_l, ps) &&
      IntervalBounds(ps) &&
      IntArray::full(st, n, st_l) *
      IntArray::full(ed, n, ed_l)
    Ensure
      exists st1 ed1 ps1,
        PairIntervals(st1, ed1, ps1) &&
        IntervalBounds(ps1) &&
        IntervalPermutation(ps, ps1) &&
        IntervalSwappedAt(ps, ps1, i, j) &&
        IntArray::full(st, n, st1) *
        IntArray::full(ed, n, ed1)
*/
{
  int start = st[i];
  int end = ed[i];
  st[i] = st[j];
  ed[i] = ed[j];
  st[j] = start;
  ed[j] = end;
}

int partition_intervals(int *st, int *ed, int intervalsSize,
                        int low, int high)
/*@ With st_l ed_l ps
    Require
      0 <= low && low <= high && high < intervalsSize &&
      PairIntervals(st_l, ed_l, ps) &&
      IntervalBounds(ps) &&
      IntArray::full(st, intervalsSize, st_l) *
      IntArray::full(ed, intervalsSize, ed_l)
    Ensure
      low <= __return && __return <= high &&
      exists st1 ed1 ps1,
        PairIntervals(st1, ed1, ps1) &&
        IntervalBounds(ps1) &&
        IntervalPermutation(ps, ps1) &&
        IntervalSameOutsideRange(ps, ps1, low, high) &&
        IntervalPartitionedAt(ps1, low, high, __return) &&
        IntArray::full(st, intervalsSize, st1) *
        IntArray::full(ed, intervalsSize, ed1)
*/
{
  int pivot_end = ed[high];
  int i = low - 1;
  /*@ Inv Assert
      exists st1 ed1 ps1,
        st == st@pre && ed == ed@pre &&
        intervalsSize == intervalsSize@pre &&
        low == low@pre && high == high@pre &&
        0 <= low && low <= high && high < intervalsSize &&
        low - 1 <= i && i < j && j <= high &&
        Zlength(st1) == intervalsSize &&
        Zlength(ed1) == intervalsSize &&
        pivot_end == ed1[high] &&
        PairIntervals(st1, ed1, ps1) &&
        IntervalBounds(ps1) &&
        LomutoScanState(ps, ps1, low, high, i, j, pivot_end) &&
        IntArray::full(st, intervalsSize, st1) *
        IntArray::full(ed, intervalsSize, ed1)
      by array_length
  */
  for (int j = low; j < high; ++j) {
    /*@ Given st1 ed1 ps1 */
    if (ed[j] <= pivot_end) {
      ++i;
      swap_intervals(st, ed, i, j) /*@ where ps = ps1 */;
    }
  }
  /*@ Given st1 ed1 ps1 */
  swap_intervals(st, ed, i + 1, high) /*@ where ps = ps1 */;
  return i + 1;
}

void quicksort_intervals_range(int *st, int *ed, int intervalsSize,
                               int left, int right)
/*@ With st_l ed_l ps
    Require
      0 <= intervalsSize && 0 <= left && -1 <= right &&
      right < intervalsSize &&
      PairIntervals(st_l, ed_l, ps) &&
      IntervalBounds(ps) &&
      IntArray::full(st, intervalsSize, st_l) *
      IntArray::full(ed, intervalsSize, ed_l)
    Ensure
      exists st1 ed1 ps1,
        PairIntervals(st1, ed1, ps1) &&
        IntervalBounds(ps1) &&
        IntervalPermutation(ps, ps1) &&
        IntervalSameOutsideRange(ps, ps1, left, right) &&
        IntervalsEndSortedRange(ps1, left, right) &&
        IntArray::full(st, intervalsSize, st1) *
        IntArray::full(ed, intervalsSize, ed1)
*/
{
  if (left < right) {
    int pivot = partition_intervals(st, ed, intervalsSize, left, right)
      /*@ where ps = ps */;
    /*@ Given st1 ed1 ps1 */
    if (pivot > left) {
      quicksort_intervals_range(st, ed, intervalsSize, left, pivot - 1)
        /*@ where ps = ps1 */;
    }

    /*@ Assert
        exists current_st current_ed current_ps,
          st == st@pre && ed == ed@pre &&
          intervalsSize == intervalsSize@pre &&
          left == left@pre && right == right@pre &&
          0 <= intervalsSize && 0 <= left && left < right &&
          right < intervalsSize &&
          left <= pivot && pivot <= right &&
          PairIntervals(current_st, current_ed, current_ps) &&
          IntervalBounds(current_ps) &&
          IntervalPermutation(ps, current_ps) &&
          IntervalSameOutsideRange(ps, current_ps, left, right) &&
          IntervalPartitionedAt(current_ps, left, right, pivot) &&
          IntervalsEndSortedRange(current_ps, left, pivot - 1) &&
          IntArray::full(st, intervalsSize, current_st) *
          IntArray::full(ed, intervalsSize, current_ed)
    */
    /*@ Given current_st current_ed current_ps */
    if (pivot < right) {
      quicksort_intervals_range(st, ed, intervalsSize, pivot + 1, right)
        /*@ where ps = current_ps */;
    }
  }
}

void quicksort_intervals(int *st, int *ed, int intervalsSize)
/*@ With st_l ed_l ps
    Require
      0 <= intervalsSize && intervalsSize <= 1000 &&
      PairIntervals(st_l, ed_l, ps) &&
      IntervalBounds(ps) &&
      IntArray::full(st, intervalsSize, st_l) *
      IntArray::full(ed, intervalsSize, ed_l)
    Ensure
      exists st1 ed1 ps1,
        PairIntervals(st1, ed1, ps1) &&
        IntervalBounds(ps1) &&
        IntervalPermutation(ps, ps1) &&
        IntervalsEndSorted(ps1) &&
        IntArray::full(st, intervalsSize, st1) *
        IntArray::full(ed, intervalsSize, ed1)
*/
{
  quicksort_intervals_range(st, ed, intervalsSize, 0, intervalsSize - 1)
    /*@ where ps = ps */;
}

int eraseOverlapIntervals(int *st, int *ed, int intervalsSize)
/*@ With st_l ed_l ps
    Require
      0 <= intervalsSize && intervalsSize <= 1000 &&
      PairIntervals(st_l, ed_l, ps) &&
      IntervalBounds(ps) &&
      IntArray::full(st, intervalsSize, st_l) *
      IntArray::full(ed, intervalsSize, ed_l)
    Ensure
      0 <= __return && __return <= intervalsSize &&
      MinimumRemovals(ps, __return) &&
      exists st1 ed1 ps1,
        PairIntervals(st1, ed1, ps1) &&
        IntervalBounds(ps1) &&
        IntervalPermutation(ps, ps1) &&
        IntervalsEndSorted(ps1) &&
        IntArray::full(st, intervalsSize, st1) *
        IntArray::full(ed, intervalsSize, ed1)
*/
{
  quicksort_intervals(st, ed, intervalsSize) /*@ where ps = ps */;
  /*@ Given st1 ed1 ps1 */

  if (intervalsSize == 0) {
    return 0;
  }

  int kept = 1;
  int last_end = ed[0];
  /*@ Inv Assert
      exists sorted_st sorted_ed sorted_ps,
        st == st@pre && ed == ed@pre &&
        intervalsSize == intervalsSize@pre &&
        1 <= i && i <= intervalsSize &&
        1 <= kept && kept <= i &&
        -10000 <= last_end && last_end <= 10000 &&
        Zlength(sorted_st) == intervalsSize &&
        Zlength(sorted_ed) == intervalsSize &&
        PairIntervals(sorted_st, sorted_ed, sorted_ps) &&
        IntervalBounds(sorted_ps) &&
        IntervalPermutation(ps, sorted_ps) &&
        IntervalsEndSorted(sorted_ps) &&
        GreedyPrefixState(sorted_ps, i, kept, last_end) &&
        IntArray::full(st, intervalsSize, sorted_st) *
        IntArray::full(ed, intervalsSize, sorted_ed)
      by array_length
  */
  for (int i = 1; i < intervalsSize; ++i) {
    if (st[i] >= last_end) {
      ++kept;
      last_end = ed[i];
    }
  }

  /*@ Assert
      exists sorted_st sorted_ed sorted_ps,
        st == st@pre && ed == ed@pre &&
        intervalsSize == intervalsSize@pre &&
        1 <= kept && kept <= intervalsSize &&
        0 <= intervalsSize - kept &&
        intervalsSize - kept <= intervalsSize &&
        PairIntervals(sorted_st, sorted_ed, sorted_ps) &&
        IntervalBounds(sorted_ps) &&
        IntervalPermutation(ps, sorted_ps) &&
        IntervalsEndSorted(sorted_ps) &&
        GreedyPrefixState(sorted_ps, intervalsSize, kept, last_end) &&
        MinimumRemovals(ps, intervalsSize - kept) &&
        IntArray::full(st, intervalsSize, sorted_st) *
        IntArray::full(ed, intervalsSize, sorted_ed)
  */

  return intervalsSize - kept;
}
