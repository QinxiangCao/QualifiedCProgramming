/*@ Extern Coq
  (PianoNodes : list Z -> list Z -> list Z -> list Z -> list Z -> list (Z * Z * Z * Z * Z))
 */
#define PIANO_LEVELS 17
/*@ Extern Coq
      (PianoSwap : list (Z * Z * Z * Z * Z) -> Z -> Z -> list (Z * Z * Z * Z * Z))
      (PianoHeapPush : list (Z * Z * Z * Z * Z) -> list (Z * Z * Z * Z * Z) -> Z -> Z -> Z * Z * Z * Z * Z -> Prop)
      (PianoHeapPop : list (Z * Z * Z * Z * Z) -> list (Z * Z * Z * Z * Z) -> Z -> Z -> Prop)
      (PianoHeapSelected : list (Z * Z * Z * Z * Z) -> Z -> Z -> Z -> Prop)
      (PianoInitialPrefix : list Z -> Z -> Z -> Z -> Z -> list (Z * Z * Z * Z * Z) -> Prop)
 */




/*@ Extern Coq
      (Power2 : Z -> Z)
      (PianoSparseTable : list Z -> list Z -> Z -> Prop)
      (PianoSparseProgress : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (PrefixArrayPrefix : list Z -> list Z -> Z -> Prop)
      (PrefixSums : list Z -> list Z -> Prop)
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
      Forall(Z::le(INT_MIN), ps) && Forall(Z::ge(INT_MAX), ps) &&
      IntArray::full(arr, n, l) *
      IntArray::undef_full(pre, n + 1) &&
      Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
    Ensure
      exists ps,
      PrefixSums(l, ps) &&
      IntArray::full(arr, n, l) *
      IntArray::full(pre, n + 1, ps)
 */
{
  pre[0] = 0;
  

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
      Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
   */
  for (int i = 0; i < n; ++i) {
    pre[i + 1] = pre[i] + arr[i];
  }
}

void build_sparse_argmax(int *pre, int len, int *st)
/*@ With (ps : list Z)
    Require 1 <= len && len <= 100001 &&
      IntArray::full(pre, len, ps) *
      IntArray::undef_full(st, len * 17)
    Ensure exists table,
      PianoSparseTable(ps, table, len) &&
      IntArray::full(pre, len, ps) *
      IntArray::full(st, len * 17, table)
 */
{
  /*@ Inv Assert exists table,
      pre == pre@pre && len == len@pre && st == st@pre &&
      1 <= len && len <= 100001 && 0 <= i && i <= len * 17 &&
      IntArray::full(pre, len, ps) *
      IntArray::seg(st, 0, i, table) * IntArray::undef_seg(st, i, len * 17)
   */
  for (int i = 0; i < len * PIANO_LEVELS; ++i) { st[i] = 0; }

  /*@ Inv Assert exists table,
      pre == pre@pre && len == len@pre && st == st@pre &&
      1 <= len && len <= 100001 && 0 <= i && i <= len &&
      PianoSparseProgress(ps, table, len, 0, i) &&
      IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, table)
   */
  for (int i = 0; i < len; ++i) { st[i * PIANO_LEVELS] = i; }

  int half = 1;
  int width = 2;
  /*@ Inv Assert exists table,
      pre == pre@pre && len == len@pre && st == st@pre &&
      1 <= len && len <= 100001 && 1 <= level && level <= 17 &&
      half == Power2(level - 1) && width == Power2(level) &&
      1 <= half && half <= 65536 && width == half + half &&
      PianoSparseProgress(ps, table, len, level, 0) &&
      IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, table)
   */
  for (int level = 1; level < PIANO_LEVELS; ++level) {
    /*@ Inv Assert exists table,
        pre == pre@pre && len == len@pre && st == st@pre &&
        1 <= len && len <= 100001 && 1 <= level && level < 17 &&
        half == Power2(level - 1) && width == Power2(level) &&
      1 <= half && half <= 65536 && width == half + half &&
        0 <= i && i <= len &&
        PianoSparseProgress(ps, table, len, level, i) &&
        IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, table)
     */
    for (int i = 0; i + width <= len; ++i) {
      int a = st[i * PIANO_LEVELS + level - 1];
      int c = st[(i + half) * PIANO_LEVELS + level - 1];
      /*@ Assert exists table,
          pre == pre@pre && len == len@pre && st == st@pre &&
          1 <= len && len <= 100001 && 1 <= level && level < 17 &&
          half == Power2(level - 1) && width == Power2(level) &&
      1 <= half && half <= 65536 && width == half + half &&
          0 <= i && i + width <= len &&
          a == Znth(i * 17 + level - 1, table, 0) &&
          c == Znth((i + half) * 17 + level - 1, table, 0) &&
          0 <= a && a < len && 0 <= c && c < len &&
          PianoSparseProgress(ps, table, len, level, i) &&
          IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, table)
       */
      if (pre[a] >= pre[c]) { st[i * PIANO_LEVELS + level] = a; }
      else { st[i * PIANO_LEVELS + level] = c; }
    }
    half = width;
    width = width * 2;
  }
}

int query_argmax(int *pre, int len, int *st, int lo, int hi)
/*@ With (ps : list Z) (st_slots : list Z)
    Require 1 <= len && len <= 100001 && 0 <= lo && lo <= hi && hi < len &&
      PianoSparseTable(ps, st_slots, len) &&
      IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, st_slots)
    Ensure lo <= __return && __return <= hi && RangeArgmax(ps, lo, hi, __return) &&
      IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, st_slots)
 */
{
  int level = 0;
  int width = 1;
  /*@ Inv Assert
      pre == pre@pre && len == len@pre && st == st@pre && lo == lo@pre && hi == hi@pre &&
      1 <= len && len <= 100001 && 0 <= lo && lo <= hi && hi < len &&
      0 <= level && level < 17 && width == Power2(level) &&
      1 <= width && width <= hi - lo + 1 &&
      PianoSparseTable(ps, st_slots, len) &&
      IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, st_slots)
   */
  while (width * 2 <= hi - lo + 1) { width = width * 2; ++level; }
  int a = st[lo * PIANO_LEVELS + level];
  int c = st[(hi - width + 1) * PIANO_LEVELS + level];
  /*@ Assert
      pre == pre@pre && len == len@pre && st == st@pre && lo == lo@pre && hi == hi@pre &&
      1 <= len && len <= 100001 && 0 <= lo && lo <= hi && hi < len &&
      0 <= level && level < 17 && width == Power2(level) &&
      1 <= width && width <= hi - lo + 1 && hi - lo + 1 < width * 2 &&
      a == Znth(lo * 17 + level, st_slots, 0) &&
      c == Znth((hi - width + 1) * 17 + level, st_slots, 0) &&
      0 <= a && a < len && 0 <= c && c < len &&
      PianoSparseTable(ps, st_slots, len) &&
      IntArray::full(pre, len, ps) * IntArray::full(st, len * 17, st_slots)
   */
  if (pre[a] >= pre[c]) { return a; }
  else { return c; }
}

void piano_set_node(int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best, int cap, int index, int value, int start, int lo, int hi, int best)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require 0 <= index && index < cap && NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure exists vals_out starts_out los_out his_out bests_out,
      NodeArrays(replace_Znth(index, mkNode(value, start, lo, hi, best), PianoNodes(vals, starts, los, his, bests)), vals_out, starts_out, los_out, his_out, bests_out) &&
      IntArray::full(heap_value, cap, vals_out) *
      IntArray::full(heap_start, cap, starts_out) *
      IntArray::full(heap_lo, cap, los_out) *
      IntArray::full(heap_hi, cap, his_out) *
      IntArray::full(heap_best, cap, bests_out)
 */
{
  heap_value[index] = value;
  heap_start[index] = start;
  heap_lo[index] = lo;
  heap_hi[index] = hi;
  heap_best[index] = best;
}

void piano_swap_node(int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best, int cap, int a, int b)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require 0 <= a && a < cap && 0 <= b && b < cap && NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure exists vals_out starts_out los_out his_out bests_out,
      NodeArrays(PianoSwap(PianoNodes(vals, starts, los, his, bests), a, b), vals_out, starts_out, los_out, his_out, bests_out) &&
      IntArray::full(heap_value, cap, vals_out) *
      IntArray::full(heap_start, cap, starts_out) *
      IntArray::full(heap_lo, cap, los_out) *
      IntArray::full(heap_hi, cap, his_out) *
      IntArray::full(heap_best, cap, bests_out)
 */
{
  int tmp_value = heap_value[a];
  heap_value[a] = heap_value[b];
  heap_value[b] = tmp_value;
  int tmp_start = heap_start[a];
  heap_start[a] = heap_start[b];
  heap_start[b] = tmp_start;
  int tmp_lo = heap_lo[a];
  heap_lo[a] = heap_lo[b];
  heap_lo[b] = tmp_lo;
  int tmp_hi = heap_hi[a];
  heap_hi[a] = heap_hi[b];
  heap_hi[b] = tmp_hi;
  int tmp_best = heap_best[a];
  heap_best[a] = heap_best[b];
  heap_best[b] = tmp_best;
}

int frontier_top_value(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(PianoNodes(vals, starts, los, his, bests)) == cap &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_value(PianoNodes(vals, starts, los, his, bests)) &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
{ return heap_value[0]; }

int frontier_top_start(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(PianoNodes(vals, starts, los, his, bests)) == cap &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_start(PianoNodes(vals, starts, los, his, bests)) &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
{ return heap_start[0]; }

int frontier_top_lo(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(PianoNodes(vals, starts, los, his, bests)) == cap &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_lo(PianoNodes(vals, starts, los, his, bests)) &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
{ return heap_lo[0]; }

int frontier_top_hi(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(PianoNodes(vals, starts, los, his, bests)) == cap &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_hi(PianoNodes(vals, starts, los, his, bests)) &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
{ return heap_hi[0]; }

int frontier_top_best(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap &&
      Zlength(PianoNodes(vals, starts, los, his, bests)) == cap &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
    Ensure
      __return == heap_top_best(PianoNodes(vals, starts, los, his, bests)) &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
{ return heap_best[0]; }

void frontier_pop_only(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 < size && size <= cap && cap <= 200000 &&
      Zlength(PianoNodes(vals, starts, los, his, bests)) == cap &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
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
      FrontierPopTop(PianoNodes(vals, starts, los, his, bests), size, slots_out) &&
      IntArray::full(heap_value, cap, vals_out) *
      IntArray::full(heap_start, cap, starts_out) *
      IntArray::full(heap_lo, cap, los_out) *
      IntArray::full(heap_hi, cap, his_out) *
      IntArray::full(heap_best, cap, bests_out)
 */
{
  if (size == 1) { return; }
  piano_set_node(heap_value, heap_start, heap_lo, heap_hi, heap_best, cap, 0,
    heap_value[size - 1], heap_start[size - 1], heap_lo[size - 1], heap_hi[size - 1], heap_best[size - 1]);
  int index = 0;
  /*@ Inv Assert exists current vals_cur starts_cur los_cur his_cur bests_cur,
      heap_value == heap_value@pre && heap_start == heap_start@pre && heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre && cap == cap@pre && size == size@pre &&
      1 < size && size <= cap && cap <= 200000 &&
      0 <= index && index < size - 1 &&
      PianoHeapPop(PianoNodes(vals, starts, los, his, bests), current, size, index) &&
      NodeArrays(current, vals_cur, starts_cur, los_cur, his_cur, bests_cur) &&
      IntArray::full(heap_value, cap, vals_cur) *
      IntArray::full(heap_start, cap, starts_cur) *
      IntArray::full(heap_lo, cap, los_cur) *
      IntArray::full(heap_hi, cap, his_cur) *
      IntArray::full(heap_best, cap, bests_cur) */
  while (index * 2 + 1 < size - 1) {
    int left = index * 2 + 1;
    int right = left + 1;
    int selected = left;
    if (right < size - 1 && heap_value[left] < heap_value[right]) { selected = right; }
    /*@ Assert exists current vals_cur starts_cur los_cur his_cur bests_cur,
      heap_value == heap_value@pre && heap_start == heap_start@pre && heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre && cap == cap@pre && size == size@pre &&
      1 < size && size <= cap && cap <= 200000 &&
      0 <= index && index < size - 1 &&
      PianoHeapPop(PianoNodes(vals, starts, los, his, bests), current, size, index) &&
      NodeArrays(current, vals_cur, starts_cur, los_cur, his_cur, bests_cur) &&
      IntArray::full(heap_value, cap, vals_cur) *
      IntArray::full(heap_start, cap, starts_cur) *
      IntArray::full(heap_lo, cap, los_cur) *
      IntArray::full(heap_hi, cap, his_cur) *
      IntArray::full(heap_best, cap, bests_cur) &&
        left == index * 2 + 1 && right == left + 1 &&
        0 <= selected && selected < size - 1 &&
        PianoHeapSelected(current, size - 1, index, selected)
     */
    if (heap_value[index] >= heap_value[selected]) { break; }
    piano_swap_node(heap_value, heap_start, heap_lo, heap_hi, heap_best, cap, index, selected);
    index = selected;
  }
}


void frontier_push(
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best,
    int cap, int size, int value, int start, int lo, int hi, int best)
/*@ With (vals : list Z) (starts : list Z) (los : list Z) (his : list Z) (bests : list Z)
    Require
      0 <= size && size < cap &&
      Zlength(PianoNodes(vals, starts, los, his, bests)) == cap &&
      NodeArrays(PianoNodes(vals, starts, los, his, bests), vals, starts, los, his, bests) &&
      NodeHeapState(PianoNodes(vals, starts, los, his, bests), size) &&
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
      FrontierPushFields(PianoNodes(vals, starts, los, his, bests), size, value, start, lo, hi, best, slots_out) &&
      IntArray::full(heap_value, cap, vals_out) *
      IntArray::full(heap_start, cap, starts_out) *
      IntArray::full(heap_lo, cap, los_out) *
      IntArray::full(heap_hi, cap, his_out) *
      IntArray::full(heap_best, cap, bests_out)
 */
{
  piano_set_node(heap_value, heap_start, heap_lo, heap_hi, heap_best, cap, size, value, start, lo, hi, best);
  int child = size;
  /*@ Inv Assert
      exists current vals_cur starts_cur los_cur his_cur bests_cur,
      heap_value == heap_value@pre && heap_start == heap_start@pre && heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre && cap == cap@pre && size == size@pre &&
      0 <= size && size < cap &&
      NodeArrays(current, vals_cur, starts_cur, los_cur, his_cur, bests_cur) &&
      IntArray::full(heap_value, cap, vals_cur) *
      IntArray::full(heap_start, cap, starts_cur) *
      IntArray::full(heap_lo, cap, los_cur) *
      IntArray::full(heap_hi, cap, his_cur) *
      IntArray::full(heap_best, cap, bests_cur) &&
      value == value@pre && start == start@pre && lo == lo@pre && hi == hi@pre && best == best@pre &&
      0 <= child && child <= size &&
      PianoHeapPush(PianoNodes(vals, starts, los, his, bests), current, size, child, mkNode(value, start, lo, hi, best))
   */
  while (child > 0) {
    int parent = (child - 1) / 2;
    /*@ Assert
      exists current vals_cur starts_cur los_cur his_cur bests_cur,
      heap_value == heap_value@pre && heap_start == heap_start@pre && heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre && cap == cap@pre && size == size@pre &&
      0 <= size && size < cap &&
      NodeArrays(current, vals_cur, starts_cur, los_cur, his_cur, bests_cur) &&
      IntArray::full(heap_value, cap, vals_cur) *
      IntArray::full(heap_start, cap, starts_cur) *
      IntArray::full(heap_lo, cap, los_cur) *
      IntArray::full(heap_hi, cap, his_cur) *
      IntArray::full(heap_best, cap, bests_cur) &&
      value == value@pre && start == start@pre && lo == lo@pre && hi == hi@pre && best == best@pre &&
      0 <= child && child <= size &&
      PianoHeapPush(PianoNodes(vals, starts, los, his, bests), current, size, child, mkNode(value, start, lo, hi, best))
    &&
      parent == (child - 1) / 2 && 0 <= parent && parent < child && child > 0
     */
    if (heap_value[parent] >= heap_value[child]) { break; }
    piano_swap_node(heap_value, heap_start, heap_lo, heap_hi, heap_best, cap, parent, child);
    child = parent;
  }
}


int build_initial_frontier(
    int *pre, int n, int L, int R, int *st,
    int cap,
    int *heap_value, int *heap_start, int *heap_lo, int *heap_hi, int *heap_best)
/*@ With (ps : list Z) (st_slots : list Z)
    Require
      1 <= n && n <= 100000 &&
      1 <= L && L <= R && R <= n &&
      n - L + 1 <= cap && cap <= 200000 &&
      Forall(Z::le(-100000000), ps) && Forall(Z::ge(100000000), ps) &&
      Zlength(ps) == n + 1 &&
      PianoSparseTable(ps, st_slots, n + 1) &&
      IntArray::full(pre, n + 1, ps) *
      IntArray::full(st, (n + 1) * 17, st_slots) *
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
      IntArray::full(st, (n + 1) * 17, st_slots) *
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
 */
{
  /*@ Inv Assert exists vals starts los his bests,
      pre == pre@pre && n == n@pre && L == L@pre && R == R@pre && st == st@pre &&
      heap_value == heap_value@pre && heap_start == heap_start@pre && heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre && cap == cap@pre &&
      1 <= n && n <= 100000 && 1 <= L && L <= R && R <= n &&
      n - L + 1 <= cap && cap <= 200000 && 0 <= i && i <= cap &&
      Forall(Z::le(-100000000), ps) && Forall(Z::ge(100000000), ps) &&
      PianoSparseTable(ps, st_slots, n + 1) &&
      IntArray::full(pre, n + 1, ps) * IntArray::full(st, (n + 1) * 17, st_slots) *
      IntArray::seg(heap_value, 0, i, vals) * IntArray::undef_seg(heap_value, i, cap) * IntArray::seg(heap_start, 0, i, starts) * IntArray::undef_seg(heap_start, i, cap) * IntArray::seg(heap_lo, 0, i, los) * IntArray::undef_seg(heap_lo, i, cap) * IntArray::seg(heap_hi, 0, i, his) * IntArray::undef_seg(heap_hi, i, cap) * IntArray::seg(heap_best, 0, i, bests) * IntArray::undef_seg(heap_best, i, cap)
   */
  for (int i = 0; i < cap; ++i) {
    heap_value[i] = 0; heap_start[i] = 0; heap_lo[i] = 0; heap_hi[i] = 0; heap_best[i] = 0;
  }
  int size = 0;
  /*@ Inv Assert exists slots vals starts los his bests,
      pre == pre@pre && n == n@pre && L == L@pre && R == R@pre && st == st@pre &&
      heap_value == heap_value@pre && heap_start == heap_start@pre && heap_lo == heap_lo@pre && heap_hi == heap_hi@pre && heap_best == heap_best@pre && cap == cap@pre &&
      1 <= n && n <= 100000 && 1 <= L && L <= R && R <= n &&
      n - L + 1 <= cap && cap <= 200000 && 0 <= size && size <= n - L + 1 &&
      1 <= start && start <= n - L + 2 && size == start - 1 &&
      Forall(Z::le(-100000000), ps) && Forall(Z::ge(100000000), ps) &&
      PianoSparseTable(ps, st_slots, n + 1) &&
      PianoInitialPrefix(ps, n, L, R, start, sublist(0, size, slots)) &&
      Zlength(slots) == cap && NodeHeapState(slots, size) && NodeArrays(slots, vals, starts, los, his, bests) &&
      IntArray::full(pre, n + 1, ps) * IntArray::full(st, (n + 1) * 17, st_slots) *
      IntArray::full(heap_value, cap, vals) *
      IntArray::full(heap_start, cap, starts) *
      IntArray::full(heap_lo, cap, los) *
      IntArray::full(heap_hi, cap, his) *
      IntArray::full(heap_best, cap, bests)
   */
  for (int start = 1; start <= n - L + 1; ++start) {
    int lo = start + L - 1;
    int hi = start + R - 1;
    if (hi > n) { hi = n; }
    int best = query_argmax(pre, n + 1, st, lo, hi);
    int value = pre[best] - pre[start - 1];

    frontier_push(heap_value, heap_start, heap_lo, heap_hi, heap_best, cap, size, value, start, lo, hi, best);
    ++size;
  }
  return size;
}

/* Read a prefix cell while borrowing the local array through a pointer. */
int piano_prefix_at(int *pre, int len, int index)
/*@ With (ps : list Z)
    Require 0 <= index && index < len && IntArray::full(pre, len, ps)
    Ensure __return == ps[index] && IntArray::full(pre, len, ps)
 */
{
  return pre[index];
}

long long superPiano(
    int *arr, int n, int k, int L, int R)
/*@ With (l : list Z)
    Require
      exists ps ans,
      1 <= n && n <= 100000 &&
      1 <= L && L <= R && R <= n &&
      1 <= k && n + k + 1 <= 200000 &&
      Zlength(l) == n &&
      PrefixSums(l, ps) &&
      Forall(Z::le(INT_MIN), ps) && Forall(Z::ge(INT_MAX), ps) &&
      SuperPianoAnswerByPrefix(ps, n, L, R, k, ans) &&
      -9223372036854775808 <= ans && ans <= 9223372036854775807 &&
      IntArray::full(arr, n, l) &&
      Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
    Ensure
      exists ps,
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      PrefixSums(l, ps) &&
      SuperPianoAnswerByPrefix(ps, n, L, R, k, __return) &&
      IntArray::full(arr, n, l)
 */
{
  int prefix[100001];
  int st[1700017];
  int heap_value[200000];
  int heap_start[200000];
  int heap_lo[200000];
  int heap_hi[200000];
  int heap_best[200000];

  int heap_cap = n + k + 1;
  /*@ Assert 
      exists ps ans,
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      heap_cap == n@pre + k@pre + 1 &&
      1 <= n && n <= 100000 &&
      1 <= L && L <= R && R <= n &&
      1 <= k && heap_cap <= 200000 &&
      Zlength(l) == n &&
      PrefixSums(l, ps) &&
      Forall(Z::le(INT_MIN), ps) && Forall(Z::ge(INT_MAX), ps) &&
      SuperPianoAnswerByPrefix(ps, n, L, R, k, ans) &&
      -9223372036854775808 <= ans && ans <= 9223372036854775807 &&
      IntArray::full(arr, n, l) *
      IntArray::undef_full(pointer_offset(prefix, 0, sizeof(int), int), n + 1) *
      IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n + 1, 100001) *
      IntArray::undef_full(pointer_offset(st, 0, sizeof(int), int), (n + 1) * 17) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n + 1) * 17, 1700017) *
      IntArray::undef_full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) &&
      Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
 */

  build_prefix(arr, n, prefix);
  /*@ Assert
      exists ps ans (st_slots : list Z),
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
      1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
      heap_cap == n@pre + k@pre + 1 &&
      Zlength(l) == n@pre &&
      PrefixSums(l, ps) &&
      Zlength(st_slots) == (n@pre + 1) * 17 &&
      Forall(Z::le(INT_MIN), ps) && Forall(Z::ge(INT_MAX), ps) &&
      SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
      IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
      IntArray::undef_full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17) *
      IntArray::undef_full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap) *
      IntArray::undef_full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap) &&
      Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
   */

  /*@ Given ps ans st_slots */
  build_sparse_argmax(prefix, n + 1, st) ;


  int hsize = build_initial_frontier(
      prefix, n, L, R, st, heap_cap,
      heap_value, heap_start, heap_lo, heap_hi, heap_best);


  long long total = 0;
  

  /*@ Inv Assert
      exists ps ans st_slots slots vals starts los his bests chosen,
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
      1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
      heap_cap == n@pre + k@pre + 1 &&
      Zlength(l) == n@pre &&
      PrefixSums(l, ps) &&
      PianoSparseTable(ps, st_slots, n@pre + 1) &&
      SuperPianoAnswerByPrefix(ps, n@pre, L@pre, R@pre, k@pre, ans) &&
      Zlength(slots) == heap_cap &&
      NodeArrays(slots, vals, starts, los, his, bests) &&
      0 <= t && t <= k@pre &&
      0 <= hsize && hsize <= heap_cap &&
      hsize + (k@pre - t) < heap_cap &&
      FrontierState(ps, n@pre, L@pre, R@pre, chosen, t, total, sublist(0, hsize, slots)) &&
      NodeHeapState(slots, hsize) &&
      (t < k@pre => 0 < hsize) &&
      IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
      IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
      IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
      IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
      IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
      IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
      IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
      Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
    */
   for (int t = 0; t < k; ++t) {
    /*@ Given slots vals starts los his bests chosen */
    int value = frontier_top_value(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) ;
    int start = frontier_top_start(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) ;
    int lo = frontier_top_lo(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) ;
    int hi = frontier_top_hi(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) ;
    int best = frontier_top_best(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) ;
    /*@ Assert
        exists ps ans st_slots slots vals starts los his bests chosen,
        arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
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
        PianoSparseTable(ps, st_slots, n@pre + 1) &&
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
        IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
        IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
        IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
        IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
        IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
        IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
        IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
        IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
        Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
     */

    /*@ Given pop_slots from slots */
    frontier_pop_only(heap_value, heap_start, heap_lo, heap_hi, heap_best, heap_cap, hsize) ;
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
        left_best = query_argmax(prefix, n + 1, st, lo, best - 1) ;
        
        left_value = piano_prefix_at(prefix, n + 1, left_best) - piano_prefix_at(prefix, n + 1, start - 1);
        has_left = 1;
      }

      if (best + 1 <= hi) {
        right_best = query_argmax(prefix, n + 1, st, best + 1, hi) ;
        
        right_value = piano_prefix_at(prefix, n + 1, right_best) - piano_prefix_at(prefix, n + 1, start - 1);
        has_right = 1;
      }

      if (has_left) {
        if (has_right) {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            PianoSparseTable(ps, st_slots, n@pre + 1) &&
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
            IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
            IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
            IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
            IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
            IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
            IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
            IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
            Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
         */
        } else {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            PianoSparseTable(ps, st_slots, n@pre + 1) &&
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
            IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
            IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
            IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
            IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
            IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
            IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
            IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
            Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
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
            ;
        hsize = hsize + 1;
      }

      if (!has_left && !has_right) {
      /*@ Assert
          exists ps ans st_slots slots vals starts los his bests chosen,
          arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
          1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
          heap_cap == n@pre + k@pre + 1 &&
          Zlength(l) == n@pre &&
          PrefixSums(l, ps) &&
          PianoSparseTable(ps, st_slots, n@pre + 1) &&
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
          IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
          IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
          IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
          IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
          IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
          IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
          IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
          IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
          Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
       */
      }

      if (has_right) {
        if (has_left) {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            PianoSparseTable(ps, st_slots, n@pre + 1) &&
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
            IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
            IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
            IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
            IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
            IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
            IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
            IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
            Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
         */
        } else {
        /*@ Assert
            exists ps ans st_slots slots vals starts los his bests chosen,
            arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
            1 <= n@pre && n@pre <= 100000 &&
            1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
            1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
            heap_cap == n@pre + k@pre + 1 &&
            Zlength(l) == n@pre &&
            PrefixSums(l, ps) &&
            PianoSparseTable(ps, st_slots, n@pre + 1) &&
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
            IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
            IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
            IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
            IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
            IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
            IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
            IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
            IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
            Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
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
            ;
        hsize = hsize + 1;
      }

      /*@ Assert
          exists ps ans st_slots slots vals starts los his bests chosen,
          arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= L@pre && L@pre <= R@pre && R@pre <= n@pre &&
          1 <= k@pre && n@pre + k@pre + 1 <= 200000 &&
          heap_cap == n@pre + k@pre + 1 &&
          Zlength(l) == n@pre &&
          PrefixSums(l, ps) &&
          PianoSparseTable(ps, st_slots, n@pre + 1) &&
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
          IntArray::undef_seg(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, 100001) *
      IntArray::undef_seg(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, 1700017) *
      IntArray::undef_seg(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::undef_seg(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, 200000) *
      IntArray::full(arr@pre, n@pre, l) *
          IntArray::full(pointer_offset(prefix, 0, sizeof(int), int), n@pre + 1, ps) *
          IntArray::full(pointer_offset(st, 0, sizeof(int), int), (n@pre + 1) * 17, st_slots) *
          IntArray::full(pointer_offset(heap_value, 0, sizeof(int), int), heap_cap, vals) *
          IntArray::full(pointer_offset(heap_start, 0, sizeof(int), int), heap_cap, starts) *
          IntArray::full(pointer_offset(heap_lo, 0, sizeof(int), int), heap_cap, los) *
          IntArray::full(pointer_offset(heap_hi, 0, sizeof(int), int), heap_cap, his) *
          IntArray::full(pointer_offset(heap_best, 0, sizeof(int), int), heap_cap, bests) &&
          Forall(Z::le(-1000), l) && Forall(Z::ge(1000), l)
       */
    }
  }

  /*@ Assert
      exists ps,
      heap_cap == n + k + 1 && 0 <= hsize && hsize <= heap_cap &&
      arr == arr@pre && n == n@pre && k == k@pre && L == L@pre && R == R@pre &&
      PrefixSums(l, ps) &&
      SuperPianoAnswerByPrefix(ps, n, L, R, k, total) &&
      IntArray::full(arr, n, l) *
      IntArray::undef_full(prefix, 100001) *
      IntArray::undef_full(st, 1700017) *
      IntArray::undef_full(heap_value, 200000) *
      IntArray::undef_full(heap_start, 200000) *
      IntArray::undef_full(heap_lo, 200000) *
      IntArray::undef_full(heap_hi, 200000) *
      IntArray::undef_full(heap_best, 200000)
   */
  return total;
}
