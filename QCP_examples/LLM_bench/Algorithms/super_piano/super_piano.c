



/*@ Extern Coq
      (ST_LEVELS : Z)
      (PrefixArrayPrefix : list Z -> list Z -> Z -> Prop)
      (PrefixSums : list Z -> list Z -> Prop)
      (SparseArgmaxBuilt : list Z -> list Z -> Z -> Prop)
      (RangeArgmax : list Z -> Z -> Z -> Z -> Prop)
      (default_node : Z * Z * Z * Z * Z)
      (mkNode : Z -> Z -> Z -> Z -> Z -> Z * Z * Z * Z * Z)
      (node_value : Z * Z * Z * Z * Z -> Z)
      (node_start : Z * Z * Z * Z * Z -> Z)
      (node_lo : Z * Z * Z * Z * Z -> Z)
      (node_hi : Z * Z * Z * Z * Z -> Z)
      (node_best : Z * Z * Z * Z * Z -> Z)
      (heap_top_node : list (Z * Z * Z * Z * Z) -> Z * Z * Z * Z * Z)
      (heap_top_value : list (Z * Z * Z * Z * Z) -> Z)
      (heap_top_start : list (Z * Z * Z * Z * Z) -> Z)
      (heap_top_lo : list (Z * Z * Z * Z * Z) -> Z)
      (heap_top_hi : list (Z * Z * Z * Z * Z) -> Z)
      (heap_top_best : list (Z * Z * Z * Z * Z) -> Z)
      (NodeArrays : list (Z * Z * Z * Z * Z) -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (NodeHeapState : list (Z * Z * Z * Z * Z) -> Z -> Prop)
      (ValidNode : list Z -> Z -> Z -> Z -> Z * Z * Z * Z * Z -> Prop)
      (ValidNodeFields : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (FrontierPushPrefix : list (Z * Z * Z * Z * Z) -> Z -> Z * Z * Z * Z * Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (FrontierPushFields : list (Z * Z * Z * Z * Z) -> Z -> Z -> Z -> Z -> Z -> Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (FrontierPopPrefix : list (Z * Z * Z * Z * Z) -> Z -> Z * Z * Z * Z * Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (FrontierPopTop : list (Z * Z * Z * Z * Z) -> Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (ChordCode : Z -> Z -> Z -> Z)
      (ValidSongCodes : list Z -> Z -> Z -> Z -> Z -> list Z -> Prop)
      (SongCodesSum : list Z -> Z -> list Z -> Z -> Prop)
      (ChosenDominatesRemaining : list Z -> Z -> Z -> Z -> list Z -> Prop)
      (NodesDisjointForSameStart : list (Z * Z * Z * Z * Z) -> Prop)
      (NodesCoverRemaining : list Z -> Z -> Z -> Z -> list Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (NodesExcludeChosen : Z -> list Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (FrontierState : list Z -> Z -> Z -> Z -> list Z -> Z -> Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (FrontierSplitState : list Z -> Z -> Z -> Z -> list Z -> Z -> Z -> list (Z * Z * Z * Z * Z) -> list (Z * Z * Z * Z * Z) -> Prop)
      (InitialFrontierState : list Z -> Z -> Z -> Z -> list (Z * Z * Z * Z * Z) -> Prop)
      (SuperPianoAnswerByPrefix : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib */

void build_prefix(int *arr, int n, int *pre)
/*@ With (l : list Z)
    Require
      exists ps,
      1 <= n && n <= 100000 &&
      Zlength(l) == n &&
      PrefixSums(l, ps) &&
      (forall (idx : Z), (0 <= idx && idx < n + 1) => (INT_MIN <= ps[idx] && ps[idx] <= INT_MAX)) &&
      IntArray::full(arr, n, l) *
      IntArray::undef_full(pre, n + 1) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (-1000 <= l[idx] && l[idx] <= 1000))
    Ensure
      exists ps,
      PrefixSums(l, ps) &&
      IntArray::full(arr, n, l) *
      IntArray::full(pre, n + 1, ps) &&
      (forall (idx : Z), (0 <= idx && idx < n + 1) => (INT_MIN <= ps[idx] && ps[idx] <= INT_MAX))
 */
{
  pre[0] = 0;
  /*@ Assert
      exists pref,
      arr == arr@pre && n == n@pre && pre == pre@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(pref) == 1 &&
      pref[0] == 0 &&
      PrefixArrayPrefix(l, pref, 0) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::seg(pre@pre, 0, 1, pref) *
      IntArray::undef_seg(pre@pre, 1, n@pre + 1) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
   */

  /*@ Inv Assert
      exists pref,
      arr == arr@pre && n == n@pre && pre == pre@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      0 <= i && i <= n@pre &&
      PrefixArrayPrefix(l, pref, i) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::seg(pre@pre, 0, i + 1, pref) *
      IntArray::undef_seg(pre@pre, i + 1, n@pre + 1) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
   */
  for (int i = 0; i < n; ++i) {
    pre[i + 1] = pre[i] + arr[i];
  }
}

void build_sparse_argmax(int *pre, int len, int *st)
/*@ With (ps : list Z) (st_slots : list Z)
    Require
      1 <= len && len <= 100001 &&
      Zlength(ps) == len &&
      Zlength(st_slots) == len * ST_LEVELS &&
      IntArray::full(pre, len, ps) *
      IntArray::undef_full(st, len * ST_LEVELS)
    Ensure
      exists st_out,
      SparseArgmaxBuilt(ps, st_out, len) &&
      IntArray::full(pre, len, ps) *
      IntArray::full(st, len * ST_LEVELS, st_out)
 */
;

int query_argmax(int *pre, int len, int *st, int lo, int hi)
/*@ With (ps : list Z) (st_slots : list Z)
    Require
      1 <= len && len <= 100001 &&
      0 <= lo && lo <= hi && hi < len &&
      SparseArgmaxBuilt(ps, st_slots, len) &&
      IntArray::full(pre, len, ps) *
      IntArray::full(st, len * ST_LEVELS, st_slots)
    Ensure
      RangeArgmax(ps, lo, hi, __return) &&
      0 <= __return && __return < len &&
      lo <= __return && __return <= hi &&
      SparseArgmaxBuilt(ps, st_slots, len) &&
      IntArray::full(pre, len, ps) *
      IntArray::full(st, len * ST_LEVELS, st_slots)
 */
;

int build_initial_frontier(
    int *pre, int n, int L, int R, int *st,
    int cap,
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best)
/*@ With (ps : list Z) (st_slots : list Z)
    Require
      1 <= n && n <= 100000 &&
      1 <= L && L <= R && R <= n &&
      n - L + 1 <= cap &&
      Zlength(ps) == n + 1 &&
      SparseArgmaxBuilt(ps, st_slots, n + 1) &&
      IntArray::full(pre, n + 1, ps) *
      IntArray::full(st, (n + 1) * ST_LEVELS, st_slots) *
      IntArray::undef_full(heap_value, cap) *
      IntArray::undef_full(heap_start, cap) *
      IntArray::undef_full(heap_lo, cap) *
      IntArray::undef_full(heap_hi, cap) *
      IntArray::undef_full(heap_best, cap)
    Ensure
      exists slots vals starts los his bests,
      __return == n - L + 1 &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, __return) &&
      InitialFrontierState(ps, n, L, R, sublist(0, __return, slots)) &&
      IntArray::full(pre, n + 1, ps) *
      IntArray::full(st, (n + 1) * ST_LEVELS, st_slots) *
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
;

int frontier_top_value(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (slots : list (Z * Z * Z * Z * Z)) (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_value(slots) &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
;

int frontier_top_start(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (slots : list (Z * Z * Z * Z * Z)) (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_start(slots) &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
;

int frontier_top_lo(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (slots : list (Z * Z * Z * Z * Z)) (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_lo(slots) &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
;

int frontier_top_hi(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (slots : list (Z * Z * Z * Z * Z)) (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_hi(slots) &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
;

int frontier_top_best(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (slots : list (Z * Z * Z * Z * Z)) (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_best(slots) &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
;

void frontier_pop_only(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (slots : list (Z * Z * Z * Z * Z)) (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      exists slots_out vals_out starts_out los_out his_out bests_out,
      Zlength(slots_out) == cap &&
      NodeArrays(slots_out, vals_out, starts_out, los_out, his_out, bests_out) &&
      NodeHeapState(slots_out, size - 1) &&
      FrontierPopTop(slots, size, slots_out) &&
      IntArray::full(heap_value, cap, vals_out) *
      IntArray::full(heap_start, cap, starts_out) *
      IntArray::full(heap_lo, cap, los_out) *
      IntArray::full(heap_hi, cap, his_out) *
      IntArray::full(heap_best, cap, bests_out)
 */
;

void frontier_push(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size, int value, int start, int lo, int hi, int best)
/*@ With (slots : list (Z * Z * Z * Z * Z)) (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z) (ps : list Z) (n0 : Z) (L0 : Z) (R0 : Z)
    Require
      0 <= size && size < cap &&
      Zlength(slots) == cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, size) &&
      ValidNodeFields(ps, n0, L0, R0, value, start, lo, hi, best) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      exists slots_out vals_out starts_out los_out his_out bests_out,
      Zlength(slots_out) == cap &&
      NodeArrays(slots_out, vals_out, starts_out, los_out, his_out, bests_out) &&
      NodeHeapState(slots_out, size + 1) &&
      FrontierPushFields(slots, size, value, start, lo, hi, best, slots_out) &&
      IntArray::full(heap_value, cap, vals_out) *
      IntArray::full(heap_start, cap, starts_out) *
      IntArray::full(heap_lo, cap, los_out) *
      IntArray::full(heap_hi, cap, his_out) *
      IntArray::full(heap_best, cap, bests_out)
 */
;

long long superPiano(
    int *arr, int n, int k, int L, int R,
    int *prefix, int *st,
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best)
/*@ With (l : list Z)
    Require
      exists ps ans,
      1 <= n && n <= 100000 &&
      1 <= L && L <= R && R <= n &&
      1 <= k && n + k + 1 <= 200000 &&
      Zlength(l) == n &&
      PrefixSums(l, ps) &&
      (forall (idx : Z), (0 <= idx && idx < n + 1) => (INT_MIN <= ps[idx] && ps[idx] <= INT_MAX)) &&
      SuperPianoAnswerByPrefix(ps, n, L, R, k, ans) &&
      -9223372036854775808 <= ans && ans <= 9223372036854775807 &&
      IntArray::full(arr, n, l) *
      IntArray::undef_full(prefix, n + 1) *
      IntArray::undef_full(st, (n + 1) * ST_LEVELS) *
      IntArray::undef_full(heap_value, n + k + 1) *
      IntArray::undef_full(heap_start, n + k + 1) *
      IntArray::undef_full(heap_lo, n + k + 1) *
      IntArray::undef_full(heap_hi, n + k + 1) *
      IntArray::undef_full(heap_best, n + k + 1) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (-1000 <= l[idx] && l[idx] <= 1000))
    Ensure
      exists ps st_slots slots vals starts los his bests,
      PrefixSums(l, ps) &&
      SuperPianoAnswerByPrefix(ps, n, L, R, k, __return) &&
      Zlength(slots) == n + k + 1 &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      IntArray::full(arr, n, l) *
      IntArray::full(prefix, n + 1, ps) *
      IntArray::full(st, (n + 1) * ST_LEVELS, st_slots) *
      IntArray::full(heap_value, n + k + 1, vals) *
      IntArray::full(heap_start, n + k + 1, starts) *
      IntArray::full(heap_lo, n + k + 1, los) *
      IntArray::full(heap_hi, n + k + 1, his) *
      IntArray::full(heap_best, n + k + 1, bests)
 */
{
  int heap_cap = n + k + 1;

  build_prefix(arr, n, prefix);
  /*@ Assert
      exists ps ans (st_slots : list Z),
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      prefix == prefix@pre && st == st@pre &&
      heap_value == heap_value@pre && heap_start == heap_start@pre &&
      heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
      1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
      heap_cap == n@pre + k@pre + 1 &&
      Zlength(l) == n@pre &&
      PrefixSums(l, ps) &&
      Zlength(st_slots) == (n@pre + 1) * ST_LEVELS &&
      (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= ps[idx] && ps[idx] <= INT_MAX)) &&
      SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(prefix@pre, n@pre + 1, ps) *
      IntArray::undef_full(st@pre, (n@pre + 1) * ST_LEVELS) *
      IntArray::undef_full(heap_value@pre, heap_cap) *
      IntArray::undef_full(heap_start@pre, heap_cap) *
      IntArray::undef_full(heap_lo@pre, heap_cap) *
      IntArray::undef_full(heap_hi@pre, heap_cap) *
      IntArray::undef_full(heap_best@pre, heap_cap) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
   */

  /*@ Given ps ans st_slots */
  build_sparse_argmax(prefix, n + 1, st) /*@ where ps = ps, st_slots = st_slots */;
  /*@ Assert
      exists ps ans st_slots,
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      prefix == prefix@pre && st == st@pre &&
      heap_value == heap_value@pre && heap_start == heap_start@pre &&
      heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
      1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
      heap_cap == n@pre + k@pre + 1 &&
      Zlength(l) == n@pre &&
      PrefixSums(l, ps) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= ps[idx] && ps[idx] <= INT_MAX)) &&
      SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
      SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(prefix@pre, n@pre + 1, ps) *
      IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
      IntArray::undef_full(heap_value@pre, heap_cap) *
      IntArray::undef_full(heap_start@pre, heap_cap) *
      IntArray::undef_full(heap_lo@pre, heap_cap) *
      IntArray::undef_full(heap_hi@pre, heap_cap) *
      IntArray::undef_full(heap_best@pre, heap_cap) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
   */

  int hsize = build_initial_frontier(
      prefix, n, L, R, st, heap_cap,
      heap_value, heap_start, heap_lo, heap_hi, heap_best);
  /*@ Assert
      exists ps ans st_slots slots vals starts los his bests,
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      prefix == prefix@pre && st == st@pre &&
      heap_value == heap_value@pre && heap_start == heap_start@pre &&
      heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
      1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
      heap_cap == n@pre + k@pre + 1 &&
      hsize == n@pre - L@pre + 1 &&
      hsize + k@pre < heap_cap &&
      Zlength(l) == n@pre &&
      PrefixSums(l, ps) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= ps[idx] && ps[idx] <= INT_MAX)) &&
      SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
      SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
      Zlength(slots) == heap_cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, hsize) &&
      InitialFrontierState(ps, n@pre, L@pre, R@pre, sublist(0, hsize, slots)) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(prefix@pre, n@pre + 1, ps) *
      IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
      IntArray::full(heap_value@pre, heap_cap, vals) *
      IntArray::full(heap_start@pre, heap_cap, starts) *
      IntArray::full(heap_lo@pre, heap_cap, los) *
      IntArray::full(heap_hi@pre, heap_cap, his) *
      IntArray::full(heap_best@pre, heap_cap, bests) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
   */

  long long total = 0;
  /*@ Assert
      exists ps ans st_slots slots vals starts los his bests,
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      prefix == prefix@pre && st == st@pre &&
      heap_value == heap_value@pre && heap_start == heap_start@pre &&
      heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
      1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
      heap_cap == n@pre + k@pre + 1 &&
      hsize == n@pre - L@pre + 1 &&
      hsize + k@pre < heap_cap &&
      total == 0 &&
      Zlength(l) == n@pre &&
      PrefixSums(l, ps) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= ps[idx] && ps[idx] <= INT_MAX)) &&
      SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
      SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
      Zlength(slots) == heap_cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      NodeHeapState(slots, hsize) &&
      FrontierState(ps, n@pre, L@pre, R@pre, nil, 0, 0, sublist(0, hsize, slots)) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(prefix@pre, n@pre + 1, ps) *
      IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
      IntArray::full(heap_value@pre, heap_cap, vals) *
      IntArray::full(heap_start@pre, heap_cap, starts) *
      IntArray::full(heap_lo@pre, heap_cap, los) *
      IntArray::full(heap_hi@pre, heap_cap, his) *
      IntArray::full(heap_best@pre, heap_cap, bests) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
   */

  /*@ Inv Assert
      exists ps ans st_slots slots vals starts los his bests chosen,
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      prefix == prefix@pre && st == st@pre &&
      heap_value == heap_value@pre && heap_start == heap_start@pre &&
      heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
      1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
      heap_cap == n@pre + k@pre + 1 &&
      Zlength(l) == n@pre &&
      PrefixSums(l, ps) &&
      SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
      SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
      Zlength(slots) == heap_cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      0 <= t && t <= k@pre &&
      0 <= hsize && hsize <= heap_cap &&
      hsize + (k@pre - t) < heap_cap &&
      FrontierState(ps, n@pre, L@pre, R@pre, chosen, t, total, sublist(0, hsize, slots)) &&
      NodeHeapState(slots, hsize) &&
      (t < k@pre => 0 < hsize) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(prefix@pre, n@pre + 1, ps) *
      IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
      IntArray::full(heap_value@pre, heap_cap, vals) *
      IntArray::full(heap_start@pre, heap_cap, starts) *
      IntArray::full(heap_lo@pre, heap_cap, los) *
      IntArray::full(heap_hi@pre, heap_cap, his) *
      IntArray::full(heap_best@pre, heap_cap, bests) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
    */
   for (int t = 0; t < k; ++t) {
    /*@ Given slots vals starts los his bests chosen */
    int value = frontier_top_value(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) /*@ where slots = slots */;
    int start = frontier_top_start(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) /*@ where slots = slots */;
    int lo = frontier_top_lo(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) /*@ where slots = slots */;
    int hi = frontier_top_hi(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) /*@ where slots = slots */;
    int best = frontier_top_best(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) /*@ where slots = slots */;
    /*@ Assert
        exists ps ans st_slots slots vals starts los his bests chosen,
        arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
        prefix == prefix@pre && st == st@pre &&
        heap_value == heap_value@pre && heap_start == heap_start@pre &&
        heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
        value == heap_top_value(slots) &&
        start == heap_top_start(slots) &&
        lo == heap_top_lo(slots) &&
        hi == heap_top_hi(slots) &&
        best == heap_top_best(slots) &&
        1 <= n@pre && n@pre <= 100000 &&
        1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
        1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
        heap_cap == n@pre + k@pre + 1 &&
        Zlength(l) == n@pre &&
        PrefixSums(l, ps) &&
        SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
        SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
        Zlength(slots) == heap_cap &&
        NodeArrays(slots, vals, starts, los, his, bests) &&
        0 <= t && t < k@pre &&
        0 < hsize && hsize <= heap_cap &&
        hsize + (k@pre - t) < heap_cap &&
        FrontierState(ps, n@pre, L@pre, R@pre, chosen, t, total, sublist(0, hsize, slots)) &&
        NodeHeapState(slots, hsize) &&
        ValidNodeFields(ps, n@pre, L@pre, R@pre, value, start, lo, hi, best) &&
        1 <= start && start <= n@pre &&
        0 <= start - 1 && start - 1 < n@pre + 1 &&
        start + L@pre - 1 <= lo &&
        0 <= lo && lo <= best && best <= hi && hi <= n@pre &&
        IntArray::full(arr@pre, n@pre, l) *
        IntArray::full(prefix@pre, n@pre + 1, ps) *
        IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
        IntArray::full(heap_value@pre, heap_cap, vals) *
        IntArray::full(heap_start@pre, heap_cap, starts) *
        IntArray::full(heap_lo@pre, heap_cap, los) *
        IntArray::full(heap_hi@pre, heap_cap, his) *
        IntArray::full(heap_best@pre, heap_cap, bests) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
     */

    /*@ Given pop_slots from slots */
    frontier_pop_only(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) /*@ where slots = pop_slots */;
    hsize = hsize - 1;

    total = total + (long long)value;

    {
      int has_left = 0;
      int left_best = 0;
      int left_value = 0;
      int has_right = 0;
      int right_best = 0;
      int right_value = 0;

      /*@ Given query_ps from ps
                  query_st_slots from st_slots */
      if (lo <= best - 1) {
        left_best = query_argmax(prefix, n + 1, st, lo, best - 1) /*@ where ps = query_ps, st_slots = query_st_slots */;
        left_value = prefix[left_best] - prefix[start - 1];
        has_left = 1;
      }

      if (best + 1 <= hi) {
        right_best = query_argmax(prefix, n + 1, st, best + 1, hi) /*@ where ps = query_ps, st_slots = query_st_slots */;
        right_value = prefix[right_best] - prefix[start - 1];
        has_right = 1;
      }

      if (has_left) {
        if (has_right) {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            prefix == prefix@pre && st == st@pre &&
            heap_value == heap_value@pre && heap_start == heap_start@pre &&
            heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
            SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
            Zlength(slots) == heap_cap &&
            NodeArrays(slots, vals, starts, los, his, bests) &&
            has_left == 1 && has_right == 1 &&
            0 <= t && t < k@pre &&
            0 <= hsize && hsize < heap_cap &&
            hsize + 1 + (k@pre - t) < heap_cap &&
            FrontierSplitState(
              ps, n@pre, L@pre, R@pre,
              cons(ChordCode(n@pre, start, best), chosen), t + 1, total,
              cons(mkNode(left_value, start, lo, best - 1, left_best),
                   cons(mkNode(right_value, start, best + 1, hi, right_best), nil)),
              sublist(0, hsize, slots)) &&
            NodeHeapState(slots, hsize) &&
            1 <= start && start <= n@pre &&
            0 <= start - 1 && start - 1 < n@pre + 1 &&
            0 <= lo && lo <= best - 1 &&
            best + 1 <= hi &&
            hi <= n@pre &&
            best - 1 <= n@pre &&
            RangeArgmax(ps, lo, best - 1, left_best) &&
            0 <= left_best && left_best < n@pre + 1 &&
            lo <= left_best && left_best <= best - 1 &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, left_value, start, lo, best - 1, left_best) &&
            RangeArgmax(ps, best + 1, hi, right_best) &&
            0 <= right_best && right_best < n@pre + 1 &&
            best + 1 <= right_best && right_best <= hi &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, right_value, start, best + 1, hi, right_best) &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, value, start, lo, hi, best) &&
            IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(prefix@pre, n@pre + 1, ps) *
            IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
            IntArray::full(heap_value@pre, heap_cap, vals) *
            IntArray::full(heap_start@pre, heap_cap, starts) *
            IntArray::full(heap_lo@pre, heap_cap, los) *
            IntArray::full(heap_hi@pre, heap_cap, his) *
            IntArray::full(heap_best@pre, heap_cap, bests) &&
            (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
         */
        } else {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            prefix == prefix@pre && st == st@pre &&
            heap_value == heap_value@pre && heap_start == heap_start@pre &&
            heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
            SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
            Zlength(slots) == heap_cap &&
            NodeArrays(slots, vals, starts, los, his, bests) &&
            has_left == 1 && has_right == 0 &&
            0 <= t && t < k@pre &&
            0 <= hsize && hsize < heap_cap &&
            hsize + 1 + (k@pre - t) < heap_cap &&
            FrontierSplitState(
              ps, n@pre, L@pre, R@pre,
              cons(ChordCode(n@pre, start, best), chosen), t + 1, total,
              cons(mkNode(left_value, start, lo, best - 1, left_best), nil),
              sublist(0, hsize, slots)) &&
            NodeHeapState(slots, hsize) &&
            1 <= start && start <= n@pre &&
            0 <= start - 1 && start - 1 < n@pre + 1 &&
            0 <= lo && lo <= best - 1 &&
            best <= hi && hi <= n@pre &&
            best - 1 <= n@pre &&
            RangeArgmax(ps, lo, best - 1, left_best) &&
            0 <= left_best && left_best < n@pre + 1 &&
            lo <= left_best && left_best <= best - 1 &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, left_value, start, lo, best - 1, left_best) &&
            hi <= best &&
            right_best == 0 &&
            right_value == 0 &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, value, start, lo, hi, best) &&
            IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(prefix@pre, n@pre + 1, ps) *
            IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
            IntArray::full(heap_value@pre, heap_cap, vals) *
            IntArray::full(heap_start@pre, heap_cap, starts) *
            IntArray::full(heap_lo@pre, heap_cap, los) *
            IntArray::full(heap_hi@pre, heap_cap, his) *
            IntArray::full(heap_best@pre, heap_cap, bests) &&
            (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
         */
        }
        /*@ Given push_ps from ps
                    push_slots from slots
                    push_vals from vals
                    push_starts from starts
                    push_los from los
                    push_his from his
                    push_bests from bests */
        frontier_push(
            heap_value, heap_start, heap_lo, heap_hi, heap_best,
            heap_cap, hsize, left_value, start, lo, best - 1, left_best)
            /*@ where slots = push_slots, vals = push_vals, starts = push_starts,
                       los = push_los, his = push_his, bests = push_bests,
                       ps = push_ps, n0 = n@pre, L0 = L@pre, R0 = R@pre */;
        hsize = hsize + 1;
      }

      if (!has_left && !has_right) {
      /*@ Assert
          exists ps ans st_slots slots vals starts los his bests chosen,
          arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
          prefix == prefix@pre && st == st@pre &&
          heap_value == heap_value@pre && heap_start == heap_start@pre &&
          heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
          1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
          heap_cap == n@pre + k@pre + 1 &&
          Zlength(l) == n@pre &&
          PrefixSums(l, ps) &&
          SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
          SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
          Zlength(slots) == heap_cap &&
          NodeArrays(slots, vals, starts, los, his, bests) &&
          has_left == 0 &&
          has_right == 0 &&
          left_best == 0 &&
          left_value == 0 &&
          right_best == 0 &&
          right_value == 0 &&
          0 <= t && t < k@pre &&
          0 <= hsize && hsize < heap_cap &&
          hsize + (k@pre - (t + 1)) < heap_cap &&
          FrontierSplitState(
            ps, n@pre, L@pre, R@pre,
            cons(ChordCode(n@pre, start, best), chosen), t + 1, total,
            nil, sublist(0, hsize, slots)) &&
          NodeHeapState(slots, hsize) &&
          1 <= start && start <= n@pre &&
          0 <= start - 1 && start - 1 < n@pre + 1 &&
          lo == best && best == hi &&
          ValidNodeFields(ps, n@pre, L@pre, R@pre, value, start, lo, hi, best) &&
          IntArray::full(arr@pre, n@pre, l) *
          IntArray::full(prefix@pre, n@pre + 1, ps) *
          IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
          IntArray::full(heap_value@pre, heap_cap, vals) *
          IntArray::full(heap_start@pre, heap_cap, starts) *
          IntArray::full(heap_lo@pre, heap_cap, los) *
          IntArray::full(heap_hi@pre, heap_cap, his) *
          IntArray::full(heap_best@pre, heap_cap, bests) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
       */
      }

      if (has_right) {
        if (has_left) {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            prefix == prefix@pre && st == st@pre &&
            heap_value == heap_value@pre && heap_start == heap_start@pre &&
            heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
            SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
            Zlength(slots) == heap_cap &&
            NodeArrays(slots, vals, starts, los, his, bests) &&
            has_left == 1 &&
            has_right == 1 &&
            0 <= t && t < k@pre &&
            0 <= hsize && hsize < heap_cap &&
            hsize + (k@pre - t) < heap_cap &&
            FrontierSplitState(
              ps, n@pre, L@pre, R@pre,
              cons(ChordCode(n@pre, start, best), chosen), t + 1, total,
              cons(mkNode(right_value, start, best + 1, hi, right_best), nil),
              sublist(0, hsize, slots)) &&
            NodeHeapState(slots, hsize) &&
            1 <= start && start <= n@pre &&
            0 <= start - 1 && start - 1 < n@pre + 1 &&
            0 <= lo && lo <= best &&
            best + 1 <= hi &&
            0 <= best + 1 && hi <= n@pre &&
            RangeArgmax(ps, best + 1, hi, right_best) &&
            0 <= right_best && right_best < n@pre + 1 &&
            best + 1 <= right_best && right_best <= hi &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, right_value, start, best + 1, hi, right_best) &&
            0 <= lo && lo <= best - 1 &&
            best - 1 <= n@pre &&
            RangeArgmax(ps, lo, best - 1, left_best) &&
            0 <= left_best && left_best < n@pre + 1 &&
            lo <= left_best && left_best <= best - 1 &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, left_value, start, lo, best - 1, left_best) &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, value, start, lo, hi, best) &&
            IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(prefix@pre, n@pre + 1, ps) *
            IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
            IntArray::full(heap_value@pre, heap_cap, vals) *
            IntArray::full(heap_start@pre, heap_cap, starts) *
            IntArray::full(heap_lo@pre, heap_cap, los) *
            IntArray::full(heap_hi@pre, heap_cap, his) *
            IntArray::full(heap_best@pre, heap_cap, bests) &&
            (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
         */
        } else {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            prefix == prefix@pre && st == st@pre &&
            heap_value == heap_value@pre && heap_start == heap_start@pre &&
            heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
            SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
            Zlength(slots) == heap_cap &&
            NodeArrays(slots, vals, starts, los, his, bests) &&
            has_left == 0 &&
            left_best == 0 &&
            left_value == 0 &&
            has_right == 1 &&
            0 <= t && t < k@pre &&
            0 <= hsize && hsize < heap_cap &&
            hsize + 1 + (k@pre - t) < heap_cap &&
            FrontierSplitState(
              ps, n@pre, L@pre, R@pre,
              cons(ChordCode(n@pre, start, best), chosen), t + 1, total,
              cons(mkNode(right_value, start, best + 1, hi, right_best), nil),
              sublist(0, hsize, slots)) &&
            NodeHeapState(slots, hsize) &&
            1 <= start && start <= n@pre &&
            0 <= start - 1 && start - 1 < n@pre + 1 &&
            0 <= lo && lo <= best &&
            best + 1 <= hi &&
            0 <= best + 1 && hi <= n@pre &&
            RangeArgmax(ps, best + 1, hi, right_best) &&
            0 <= right_best && right_best < n@pre + 1 &&
            best + 1 <= right_best && right_best <= hi &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, right_value, start, best + 1, hi, right_best) &&
            ValidNodeFields(ps, n@pre, L@pre, R@pre, value, start, lo, hi, best) &&
            IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(prefix@pre, n@pre + 1, ps) *
            IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
            IntArray::full(heap_value@pre, heap_cap, vals) *
            IntArray::full(heap_start@pre, heap_cap, starts) *
            IntArray::full(heap_lo@pre, heap_cap, los) *
            IntArray::full(heap_hi@pre, heap_cap, his) *
            IntArray::full(heap_best@pre, heap_cap, bests) &&
            (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
         */
        }
        /*@ Given right_ps from ps
                    right_slots from slots
                    right_vals from vals
                    right_starts from starts
                    right_los from los
                    right_his from his
                    right_bests from bests */
        frontier_push(
            heap_value, heap_start, heap_lo, heap_hi, heap_best,
            heap_cap, hsize, right_value, start, best + 1, hi, right_best)
            /*@ where slots = right_slots, vals = right_vals, starts = right_starts,
                       los = right_los, his = right_his, bests = right_bests,
                       ps = right_ps, n0 = n@pre, L0 = L@pre, R0 = R@pre */;
        hsize = hsize + 1;
      }

      /*@ Assert
          exists ps ans st_slots slots vals starts los his bests chosen,
          arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
          prefix == prefix@pre && st == st@pre &&
          heap_value == heap_value@pre && heap_start == heap_start@pre &&
          heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
          1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
          heap_cap == n@pre + k@pre + 1 &&
          Zlength(l) == n@pre &&
          PrefixSums(l, ps) &&
          SparseArgmaxBuilt(ps, st_slots, n@pre + 1) &&
          SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
          Zlength(slots) == heap_cap &&
          NodeArrays(slots, vals, starts, los, his, bests) &&
          0 <= has_left && has_left <= 1 &&
          0 <= has_right && has_right <= 1 &&
          0 <= left_best && left_best < n@pre + 1 &&
          0 <= right_best && right_best < n@pre + 1 &&
          INT_MIN <= left_value && left_value <= INT_MAX &&
          INT_MIN <= right_value && right_value <= INT_MAX &&
          0 <= t && t < k@pre &&
          0 <= hsize && hsize < heap_cap &&
          hsize + (k@pre - (t + 1)) < heap_cap &&
          FrontierState(
            ps, n@pre, L@pre, R@pre,
            cons(ChordCode(n@pre, start, best), chosen), t + 1, total,
            sublist(0, hsize, slots)) &&
          NodeHeapState(slots, hsize) &&
          ValidNodeFields(ps, n@pre, L@pre, R@pre, value, start, lo, hi, best) &&
          1 <= start && start <= n@pre &&
          0 <= start - 1 && start - 1 < n@pre + 1 &&
          start + L@pre - 1 <= lo &&
          0 <= lo && lo <= best && best <= hi && hi <= n@pre &&
          IntArray::full(arr@pre, n@pre, l) *
          IntArray::full(prefix@pre, n@pre + 1, ps) *
          IntArray::full(st@pre, (n@pre + 1) * ST_LEVELS, st_slots) *
          IntArray::full(heap_value@pre, heap_cap, vals) *
          IntArray::full(heap_start@pre, heap_cap, starts) *
          IntArray::full(heap_lo@pre, heap_cap, los) *
          IntArray::full(heap_hi@pre, heap_cap, his) *
          IntArray::full(heap_best@pre, heap_cap, bests) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (-1000 <= l[idx] && l[idx] <= 1000))
       */
    }
  }

  return total;
}
