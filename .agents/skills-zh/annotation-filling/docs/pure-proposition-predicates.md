# Pure Proposition Predicates in Annotation

This guide is only for the annotation phase: how to choose and write existing pure proposition predicates in C annotations and case-level specs. Rocq proof-side unfolding, bridging, rewriting, and helper lemmas belong in `group-worker-proving`.

Core rule: write the mathematical fact that the program must maintain. Prefer existing semantic predicates, do not expose proof-facing structures just to make a proof convenient, and do not duplicate an existing predicate in `formal_case_lib`.

## Importing Names in C Annotation

When a C annotation directly mentions a Rocq pure predicate, declare the name at the top of the C file:

```c
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (strict_lowerbound : Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sortArray_lib */
```

Use these rules:

- Put names that appear in annotation text in `Extern Coq`.
- Import the case lib or shared lib that makes those names available to generated Rocq files.
- If the predicate comes from the current `formal_case_lib`, call the predicate by name in annotation; do not copy the definition body into C annotation.
- If an existing lib already has the same meaning, use that name. Do not add duplicate names such as `increasing_aux`, `NondecreasingZList`, or `StrictlyIncreasingZList`.

## Function Specs

Function specs should state required input/output mathematical facts:

```c
/*@ With (l : list Z)
    Require
      Zlength(l) == numsSize &&
      1 <= numsSize && numsSize <= 50000 &&
      IntArray::full(nums, numsSize, l)
    Ensure
      exists l1,
      Permutation(l, l1) &&
      increasing(l1) &&
      Zlength(l1) == numsSize &&
      IntArray::full(__return, numsSize, l1)
 */
```

Selection rules:

- Sorted result: write `Permutation(l, l1) && increasing(l1)`, or `decreasing(l1)` when the result is descending.
- Sum result: write `__return == sum(l)`; in loops, maintain facts such as `ret == sum(sublist(0, i, l))`.
- Maximum, minimum, or optimum value: define a clear mathematical predicate such as `MinimizedMaxSegmentSum(l, m, ans)` in `formal_case_lib`, then call that predicate from `Require` / `Ensure`.
- Still state length, element range, and memory facts explicitly, such as `Zlength(l) == n`, `IntArray::full(a, n, l)`, and needed quantified range facts.

Do not write a spec as “the C program ran this recursive simulation.” Specs should describe input/output relations, not mirror the implementation.

## Assertions and Loop Invariants

Intermediate assertions and loop invariants should describe facts true at the current program point:

```c
/*@ Inv Assert
    exists l1 l2 l0,
      l == app(l1, l2) &&
      i == Zlength(l1) &&
      Permutation(l1, l0) &&
      increasing(l0) &&
      IntArray::full(nums, numsSize, app(l0, l2))
 */
```

For insertion sort, bubble sort, partitioning, and staged processing, prefer:

- Processed/unprocessed split: `l == app(done, todo)`, `i == Zlength(done)`.
- Processed part properties: `increasing(sorted_done)`, `Permutation(done, sorted_done)`.
- Boundary facts: `upperbound(pivot, left_part)`, `lowerbound(pivot, right_part)`, `strict_upperbound(x, l)`, `strict_lowerbound(x, l)`.
- Current candidate answer: `MinimizedMaxSegmentSum(l, m, res)`, `left <= res && res <= right`.
- Accumulated value: `ret == sum(sublist(0, i, l))`.

Do not replace an invariant with proof-facing predicates such as `mono_nondec(l)` or `mono_inc(idxs)` just to help later proof, unless the spec truly needs a strict index relation and no better annotation-facing predicate exists.

## Existing Predicates

### ListLib

Common annotation-facing names:

- `increasing(l)`: nondecreasing order. Use this first for sorted results, sorted prefixes, and sorted suffixes.
- `decreasing(l)`: nonincreasing order.
- `strict_decreasing(l)`: strictly decreasing order.
- `upperbound(x, l)` / `upper_bound(x, l)`: `x` is an upper bound of every element.
- `strict_upperbound(x, l)`: `x` is a strict upper bound.
- `lowerbound(x, l)` / `lower_bound(x, l)`: `x` is a lower bound of every element.
- `strict_lowerbound(x, l)`: `x` is a strict lower bound.
- `sum(l)`: lightweight `list Z` sum; suitable for `sum(l)` and `sum(sublist(lo, hi, l))`.
- `Zlist_max(l, lo)`: legacy list maximum computation; for new optimization specs, prefer a case-level predicate built from `MaxMinLib`.

Examples:

```c
Permutation(l1, l0) && increasing(l0)
strict_lowerbound(key, right_part)
ret == sum(sublist(0, i, l))
```

### MonotonicList

`mono_nondec`, `mono_noninc`, `mono_inc`, and `mono_dec` are primarily proof-facing predicates. Usually do not write them in annotation.

Default annotation choices:

- Ordinary ascending order: write `increasing(l)`, not `mono_nondec(l)`.
- Ordinary descending order: write `decreasing(l)`, not `mono_noninc(l)`.
- Strict descending order: write `strict_decreasing(l)`.
- Strict ascending order: if no annotation-facing business predicate exists, first consider defining a clear case-level semantic predicate. Expose `mono_inc(idxs)` in annotation only when the spec genuinely talks about a strictly increasing index sequence.

### MaxMinLib

Use `MaxMinLib` in `formal_case_lib` to define problem semantics, then let C annotation call the wrapper predicate.

Recommended pattern: define a mathematical predicate such as `MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop` in `formal_case_lib`, then declare and call only that name in C annotation:

`formal_case_lib` side:

```coq
Require Import SimpleC.EE.QCP_demos_LLM.MaxMinLib.

Definition SegmentFeasible (l : list Z) (m cap : Z) : Prop := ...

Definition MinimizedMaxSegmentSum (l : list Z) (m ans : Z) : Prop :=
  min_value_of_subset
    (fun v => exists parts, PartitionMaxSegmentSum l m parts v)
    ans.
```

```c
/*@ Extern Coq (MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop) */

/*@ With (l : list Z)
    Require exists ans,
      MinimizedMaxSegmentSum(l, m, ans) &&
      0 <= ans && ans <= 1000000000 &&
      IntArray::full(arr, n, l)
    Ensure
      MinimizedMaxSegmentSum(l, m, __return) &&
      IntArray::full(arr, n, l)
 */
```

Do not place a long search process directly in annotation. Define “maximum”, “minimum”, or “optimum” as a mathematical predicate and maintain it in invariants when needed:

```c
exists res,
  left <= res && res <= right &&
  MinimizedMaxSegmentSum(l, m, res)
```

For binary-answer programs, split the spec into:

- `CanX(l, args, cap)`: candidate `cap` is feasible.
- `CannotX(l, args, cap)`: candidate `cap` is infeasible.
- `OptimalX(l, args, ans)`: `ans` is the mathematical optimum.

The C loop keeps `left <= ans <= right`; proof-side helper lemmas connect `CanX` / `CannotX` to the optimum bounds. See `docs/correct-examples/binary-search-annotation.md`.

Do not write raw `min_value_of_subset` or `max_value_of_subset` formulas in every C invariant. Put them behind a business predicate in `formal_case_lib`, and expose only the business predicate in C.

### SumLib

For ordinary array/list segment sums, keep the annotation simple:

```c
ret == sum(sublist(0, i, l))
```

If the spec needs indexed ranges, finite sets, or two-dimensional region sums, first wrap the `SumLib` meaning in a business predicate in `formal_case_lib`, then call that predicate from annotation. Do not put complex finite-set formulas into every invariant unless the formula is short and improves readability.

`formal_case_lib` side:

```coq
Require Import SimpleC.EE.QCP_demos_LLM.SumLib.

Definition RangeContribution (l : list Z) (lo hi acc : Z) : Prop :=
  acc = sum_Z_range lo hi (fun i => Znth i l 0).
```

Prefer:

```c
Prefix2DSum(grid, rows, cols, i, j, acc)
```

instead of repeatedly expanding a two-dimensional sum definition in each invariant.

For one-dimensional list sums, prefer the lightweight list form in annotation:

```c
acc == sum(sublist(lo, hi, l))
```

Bridge to `SumLib` in proof only when the helper naturally needs finite ranges, monotonicity, splitting, or indexed maps.

## Designing New Predicates and Invariants

When existing predicates are not enough, design the new predicate as a compact mathematical relation, not as an executable list program.

Predicate design rules:

- Avoid defining list properties with `Fixpoint` when a direct logical statement is clear. Prefer `forall` / `exists` over recursive traversal definitions.
- For elementwise list facts, write index-based statements with `Znth` and `Zlength`, for example `forall i, 0 <= i < Zlength l -> P (Znth i l d)`.
- For segment facts, write them over `sublist lo hi l` or quantify over `lo <= i < hi`; do not encode the same idea as a custom recursive list scanner.
- Use `Inductive` only after checking that its induction principle and constructors will be convenient for the expected proofs. A semantic predicate with many constructors often makes generated goals and proof search heavier.
- If a property naturally has many fields or branches, consider wrapping the facts in a `Record` with named fields. Too many inductive branches can slow Rocq compilation and make goals harder to read.
- Keep new predicates stable under small implementation changes. A good predicate describes the mathematical state, not the exact loop step that produced it.

Invariant writing rules:

- Prefer short `forall` facts for preserved properties, especially range, bound, sortedness-by-index, and per-element constraints.
- If the invariant selects one element, use `Znth i l d` directly.
- If the invariant selects a segment, use `sublist lo hi l` directly.
- Do not split a list only to expose one element, for example avoid shapes like `l == app(sublist(0, i, l), cons(a, sublist(i + 1, n, l)))` when `a == Znth i l d` states the same observation.
- Use `app` decomposition when the algorithm really maintains separately owned or separately permuted pieces, such as processed prefix and unprocessed suffix. Do not use it as a default way to read one value.
- Keep invariants readable. A smaller invariant usually produces smaller generated goals and gives Rocq less irrelevant structure to compile and prove through.

Preferred shapes:

```c
forall i, 0 <= i && i < n => lower <= Znth(i, l, 0) && Znth(i, l, 0) <= upper
cur == Znth(i, l, 0)
window == sublist(lo, hi, l)
```

Bubble sort gives a good inner-loop pattern:

```c
exists a,
  Zlength(a) == n &&
  0 <= i && i < n - 1 &&
  0 <= j && j <= n - 1 - i &&
  Permutation(l, a) &&
  increasing(sublist(n - i, n, a)) &&
  (forall (p: Z) (q: Z),
    (0 <= p && p < n - i && n - i <= q && q < n) =>
    (Znth(p, a, 0) <= Znth(q, a, 0))) &&
  (forall (p: Z),
    (0 <= p && p < j) =>
    (Znth(p, a, 0) <= Znth(j, a, 0))) &&
  IntArray::full(arr, n, a)
```

This is concise because the sorted suffix is expressed as `increasing(sublist(n - i, n, a))`, the boundary between unsorted prefix and sorted suffix is a `forall` over indices, and the current inner-loop maximum candidate is written directly with `Znth(j, a, 0)`.

Avoid:

```c
l == app(sublist(0, i, l), cons(a, sublist(i + 1, n, l))) &&
a == Znth(i, l, 0)
```

unless the prefix, selected element, and suffix are separately meaningful to the algorithm.

For the bubble-sort inner loop, do not rewrite the invariant into a shape that repeatedly exposes `j` by decomposing the list:

```c
a == app(left, cons(key, right)) &&
left == sublist(0, j, a) &&
right == sublist(j + 1, n, a) &&
increasing(sublist(n - i, n, a)) &&
...
```

That form adds extra equalities and list-shape obligations without explaining the mathematical fact better. Keep the list whole and use `Znth` / `sublist` for observations.

## Before Adding a Predicate

Before adding a new `formal_case_lib` definition, ask:

- Can `increasing` / `decreasing` express the ordering property directly?
- Can `upperbound` / `lowerbound` express the boundary property directly?
- Can `sum(sublist(...))` express the segment accumulation directly?
- Should maximum, minimum, or optimum values be wrapped with `MaxMinLib` in a business predicate?
- Should range, finite-set, or two-dimensional sums be wrapped with `SumLib` in a business predicate?
- Is the new definition mathematical semantics, or is it copying the C loop?
- Can the property be written as `forall` / `exists` over indices or segments instead of as a list `Fixpoint`?
- Would an `Inductive` definition make the proof structure clearer, or would it introduce too many branches?

Add a new definition only when existing predicates cannot express the intended semantics clearly. New definitions should improve annotation readability and spec stability, not serve one local proof trick.

## Avoid

Do not write these in C annotation:

```c
/* Exposes a proof-facing predicate directly. */
mono_nondec(sorted_part)

/* Duplicates an existing ordering predicate. */
NondecreasingZList(l)

/* Mirrors the loop body as a recursive state machine. */
LoopStateAfterKSteps(...)
```

Prefer:

```c
increasing(sorted_part)
decreasing(sorted_part)
lowerbound(pivot, right_part)
ret == sum(sublist(0, i, l))
MinimizedMaxSegmentSum(l, m, res)
```
