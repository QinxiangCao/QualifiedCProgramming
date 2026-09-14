# Concise Predicate Examples

## 1. One Array Scan

Goal: return the maximum array value.

Reuse max_value_of_subset for the final result. The loop progress is:

    best is the maximum of sublist 0 i l

When max_value_of_subset states this directly, combine it with sublist in the invariant instead of defining PrefixMaximum.

The invariant needs only:

    1 <= i <= n
    + best is the maximum of sublist 0 i l
    + IntArray::full(a, n, l)

State i < n where the next a[i] access needs it. Do not repeat Zlength l = n or 0 <= n already supplied by the array resource.

Plan:

    {
      "version": 2,
      "status": "ready",
      "function_specs": [
        {"name": "array_max", "meaning": "returns the maximum value of the input array"}
      ],
      "loop_invariants": [
        {"location": "array_max: scan loop", "progress": "best is the maximum of the processed prefix"}
      ],
      "new_predicates": [],
      "vc_comparisons": []
    }

## 2. RMQ

Define the final meaning once:

- RangeMaximum states an interval maximum using the existing maximum interface;
- SparseTableBuilt refers to RangeMaximum as the interface between build and query;
- BuiltLevels refers to RangeMaximum as the only construction progress predicate.

In this RMQ example, `build` contains table zeroing, base-column construction, and level-by-level construction, while `query` contains the power-search loop. The original annotations appear first, followed by the analysis, reduced shape, and mapping of all eight definitions.

### Original C Annotation

These excerpts retain the fields directly relevant to predicate duplication and omit other execution ranges from the same assertions.

The inner construction loop carries both completed old levels and the current-level prefix:

~~~c
/*@ Inv Assert
    exists st_l,
    1 <= j && j < K &&
    half == Power2(j - 1) &&
    len == Power2(j) &&
    len == half * 2 &&
    0 <= i && i <= n &&
    BuiltLevels(l, st_l, K, n, j) &&
    LevelPrefixBuilt(l, st_l, K, n, j, i) &&
    IntArray::full(arr, n, l) *
    IntArray::full(st, n * K, st_l)
 */
for (int i = 0; i + len <= n; ++i) {
  int a = st[i * K + j - 1];
  int b = st[(i + half) * K + j - 1];
  if (a >= b) {
    st[i * K + j] = a;
  } else {
    st[i * K + j] = b;
  }
}
~~~

The query loop states the range of pow and also invokes LogSearchState:

~~~c
/*@ Inv Assert
    len == right - left + 1 &&
    1 <= len && len <= n &&
    0 <= k && k < K &&
    1 <= pow && pow <= len &&
    LogSearchState(len, k, pow) &&
    SparseTableBuilt(l, st_l, K, n) &&
    IntArray::full(st, n * K, st_l)
 */
while (pow * 2 <= len) {
  pow = pow * 2;
  k++;
}
~~~

### Original Rocq Predicates

The three construction predicates repeat RangeMaximum and differ only in the completed range:

~~~coq
Definition BaseColumnBuilt
    (l table : list Z) (K upto : Z) : Prop :=
  forall row,
    0 <= row < upto ->
    RangeMaximum l row (row + 1)
      (Znth (row * K) table 0).

Definition BuiltLevels
    (l table : list Z) (K n levels_done : Z) : Prop :=
  forall row level,
    0 <= row /\
    0 <= level < levels_done /\
    row + Power2 level <= n ->
    RangeMaximum l row (row + Power2 level)
      (Znth (row * K + level) table 0).

Definition LevelPrefixBuilt
    (l table : list Z) (K n level upto : Z) : Prop :=
  forall row,
    0 <= row < upto ->
    row + Power2 level <= n ->
    RangeMaximum l row (row + Power2 level)
      (Znth (row * K + level) table 0).

Definition LogSearchState (len k pow : Z) : Prop :=
  pow = Power2 k /\ Power2 k <= len.
~~~

### Analysis

- BaseColumnBuilt is the current prefix at level = 0.
- The old BuiltLevels describes every complete level before level.
- LevelPrefixBuilt describes the current prefix of level.
- One BuiltLevels predicate with level and prefix parameters covers all three.
- SparseTableBuilt only fixes the completed BuiltLevels parameters and remains as the build/query interface.
- LogSearchState wraps two short relations that fit directly in the invariant.
- ZeroedPrefix does not connect to SparseTableBuilt or query; the zeroing loop needs only its range and array resources.
- The n/K capacity bounds, n < Power2(K), and query interval bounds still support C safety, preservation of k < K, and final table indices; predicate reduction does not remove those consumed conditions.

### Reduced Rocq Shape

RangeMaximum refers directly to the core maximum predicate:

~~~coq
From MaxMinLib Require Import MaxMin Interface.

Definition RangeMaximum
    (l : list Z) (lo hi ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun index => lo <= index < hi)
    (fun index => Znth index l 0)
    ans.
~~~

One BuiltLevels predicate covers complete old levels and the current-level prefix:

~~~coq
Definition BuiltLevels
    (l table : list Z)
    (K n level prefix : Z) : Prop :=
  (forall row done_level,
      0 <= row /\
      0 <= done_level < level /\
      row + Z.pow 2 done_level <= n ->
      RangeMaximum l row (row + Z.pow 2 done_level)
        (Znth (row * K + done_level) table 0)) /\
  (forall row,
      0 <= row < prefix ->
      row + Z.pow 2 level <= n ->
      RangeMaximum l row (row + Z.pow 2 level)
        (Znth (row * K + level) table 0)).

Definition SparseTableBuilt
    (l table : list Z) (K n : Z) : Prop :=
  BuiltLevels l table K n K 0.
~~~

The corresponding C Extern list retains only RangeMaximum, BuiltLevels, SparseTableBuilt, and a transparent Power2 when annotation syntax actually needs it.

### Reduced C Annotation Shape

The inner construction loop uses one progress predicate:

~~~c
/*@ Inv Assert
    exists st_l,
    arr == arr@pre && n == n@pre &&
    K == K@pre && st == st@pre &&
    1 <= n && n <= 100000 &&
    1 <= K && K <= 30 &&
    n * K <= 1000000 &&
    n < Power2(K) &&
    1 <= j && j < K &&
    half == Power2(j - 1) &&
    len == Power2(j) &&
    len == half * 2 &&
    0 <= i && i <= n &&
    BuiltLevels(l, st_l, K, n, j, i) &&
    IntArray::full(arr, n, l) *
    IntArray::full(st, n * K, st_l)
 */
~~~

The query loop states the power relation directly:

~~~c
/*@ Inv Assert
    st == st@pre && n == n@pre && K == K@pre &&
    left == left@pre && right == right@pre &&
    1 <= n && n <= 100000 &&
    1 <= K && K <= 30 &&
    n * K <= 1000000 &&
    n < Power2(K) &&
    0 <= left && left <= right && right < n &&
    len == right - left + 1 &&
    1 <= len && len <= n &&
    0 <= k && k < K &&
    pow == Power2(k) &&
    1 <= pow && pow <= len &&
    SparseTableBuilt(l, st_l, K, n) &&
    IntArray::full(st, n * K, st_l)
 */
~~~

| Current definition | Result |
|---|---|
| Power2 | prefer the existing power operation |
| RangeMaximum | retain and refer directly to the core maximum predicate |
| ZeroedPrefix | remove |
| BaseColumnBuilt | merge into BuiltLevels |
| BuiltLevels | retain |
| LevelPrefixBuilt | merge into BuiltLevels |
| SparseTableBuilt | retain |
| LogSearchState | remove and write the short equalities directly in the invariant |

The reduced reference chain is:

    core maximum predicate
      -> RangeMaximum
      -> BuiltLevels / SparseTableBuilt
      -> build / query annotations

Do not add CellMaximum or LevelMaximum around RangeMaximum. Do not re-expand the maximum definition independently inside BuiltLevels and SparseTableBuilt.

Plan:

    {
      "version": 2,
      "status": "ready",
      "function_specs": [
        {"name": "build", "meaning": "builds a query table whose valid cells are interval maxima"},
        {"name": "query", "meaning": "returns the maximum value in the requested interval"}
      ],
      "loop_invariants": [
        {"location": "build: zero loop", "progress": "idx table cells have been visited by zeroing"},
        {"location": "build: base-column loop", "progress": "the first i rows of level 0 are singleton interval maxima"},
        {"location": "build: outer level loop", "progress": "every level before j consists of interval maxima"},
        {"location": "build: inner row loop", "progress": "levels before j and the first i rows of level j are interval maxima"},
        {"location": "query: power loop", "progress": "pow is the current power of two not exceeding the interval length"}
      ],
      "new_predicates": [
        {
          "name": "RangeMaximum",
          "meaning": "a value is the maximum of a specified interval of the input list",
          "why_needed": "the query result and every table cell share this interval property"
        },
        {
          "name": "SparseTableBuilt",
          "meaning": "every valid table cell satisfies RangeMaximum",
          "why_needed": "build and query need one table interface"
        },
        {
          "name": "BuiltLevels",
          "meaning": "completed levels and the current prefix satisfy RangeMaximum",
          "why_needed": "construction repeatedly uses this progress across levels and the current prefix"
        }
      ],
      "vc_comparisons": []
    }

List Power2 only when annotation syntax requires a referable name. Omit it when the power expression can be written directly.

## 3. Two-Level DP

First define the mathematical optimum returned by the function. If the caller does not read the complete DP table, the top-level Ensure does not promise every cell.

Outer-loop progress:

    the first rows_done rows are optima for their subproblems

Inner-loop progress:

    completed rows remain correct and the first cells_done cells of the current row are correct

If one predicate with rows_done and cells_done parameters states both sentences clearly, keep that one predicate. Do not stack RowsDone, RowPrefixDone, CellCorrect, and TableShape. Express TableShape with array resources and direct ranges.

## 4. Decide Whether a Predicate Is Needed

Check:

1. Does it state mathematics rather than C control state?
2. Is a direct combination of core predicates already clear?
3. Does the same substantial formula occur in several specifications, helpers, or invariants?
4. Does every parameter contribute to the meaning?
5. Does every use refer to the same definition?

Do not add it when either of the first two checks fails. A once-used name may remain when it directly names a problem concept. Do not retain a wrapper around one range, equality, or existing predicate.

## 5. Retry

Compare the proposition text in the old and current manuals directly:

    {
      "source": {
        "attempt": "case-vc-proving-r1:group_01",
        "name": "proof_of_query_entail_wit_3",
        "annotation_location": "query power loop exit"
      },
      "current": ["proof_of_query_entail_wit_3"],
      "old_gap": "the exit state lacks pow <= len",
      "change": "add pow <= len directly to the query loop invariant",
      "result": "resolved"
    }

Use unresolved and continue editing the current attempt while the gap remains.
