# Pure Proposition Predicates in Annotation

This file explains representation choices for finite quantification, unique witnesses, and higher-order existentials. The plan records only predicates added by the current case; the case library remains the source of their complete definitions.

This guide is only for the annotation phase: how to choose and write existing pure proposition predicates in C annotations and case-level specs. Rocq proof-side unfolding, bridging, rewriting, and helper lemmas belong in `group-worker-proving`.

Core rule: write the mathematical fact that the program must maintain. Prefer existing semantic predicates, do not expose proof-facing structures just to make a proof convenient, and do not duplicate an existing predicate in `formal_case_lib`.

Follow [knowledge rules §0–2 and §5–6](spec-and-contract-knowledge.md) for the range/resource boundaries of result and progress predicates and for required library reuse. The examples below follow those constraints.

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
      1 <= numsSize && numsSize <= 50000 &&
      IntArray::full(nums, numsSize, l)
    Ensure
      exists l1,
      Permutation(l, l1) &&
      increasing(l1) &&
      IntArray::full(__return, numsSize, l1)
 */
```

Selection rules:

- Sorted result: write `Permutation(l, l1) && increasing(l1)`, or `decreasing(l1)` when the result is descending.
- Sum result: write `__return == sum(l)`; in loops, maintain facts such as `ret == sum(sublist(0, i, l))`.
- Maximum, minimum, or optimum value: use `min_value_of_subset` / `max_value_of_subset` from `MaxMinLib`; do not define `IsMinimum` / `IsMaximum` or another synonymous interface. When a problem or cross-function interface needs a name, retain one case predicate that directly reuses the library semantics.
- Still state the element ranges and memory facts the algorithm genuinely needs. `IntArray::full(a, n, l)` already includes `Zlength(l) == n` and `0 <= n`, so do not repeat them.
- Expand input sizes, element ranges, and safety conditions directly in `Require`; do not wrap them in `SizeSafe`, `InputValues`, `InputValid`, or `InputBound`. Use `Forall` for index-independent element ranges. Neither result nor progress predicates contain these premises or ownership. The mathematical part of `Ensure` promises only the final output and returns resources separately.

Do not write a spec as “the C program ran this recursive simulation.” Specs should describe input/output relations, not mirror the implementation.

## Assertions and Loop Invariants

Intermediate assertions and loop invariants should describe facts true at the current program point:

```c
/*@ Inv Assert
    exists l1 l2 l0,
      nums == nums@pre && numsSize == numsSize@pre &&
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
- `sum(l)`: the lightweight `list Z` sum from `AUXLib.ListLib`, suitable for `sum(l)` and `sum(sublist(lo, hi, l))`; do not confuse it with `SumLib.Sum.sum P f`.
- `Zlist_max(l, lo)`: legacy list maximum computation; extrema in new specifications must use `min_value_of_subset` / `max_value_of_subset` from `MaxMinLib`, including inside any necessary case predicate.

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
- Strict ascending order: use a strict-monotonicity interface already present in the dependencies. Use `mono_inc(idxs)` when the specification genuinely talks about a strictly increasing index sequence; do not define a synonymous case predicate.

### MaxMinLib

Extrema must use `min_value_of_subset` / `max_value_of_subset`. When the problem output needs a name, retain one problem predicate in `formal_case_lib` and make it refer directly to `MaxMinLib`; C annotations, helpers, and invariants call that name without another wrapper layer.

Recommended pattern: define a mathematical predicate such as `MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop` in `formal_case_lib`, then declare and call only that name in C annotation:

On the `formal_case_lib` side, this fragment uses the example library's `PartitionMaxSegmentSum : list Z -> Z -> Z -> Prop` and shows only the extremum layer. Its candidates are maximum segment-sum values of legal partitions, without input ranges or C safety conditions.

```coq
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import MaxMinLib.MaxMin.

Definition MinimizedMaxSegmentSum (l : list Z) (m ans : Z) : Prop :=
  min_value_of_subset Z.le
    (fun v : Z => PartitionMaxSegmentSum l m v)
    (fun v : Z => v)
    ans.
```

Supply all four arguments: comparison relation, candidate set, measure, and result. If a problem permits an empty candidate set, retain its sentinel / `NO` branch according to the output format.

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

The C loop keeps `left <= ans <= right`; proof-side helper lemmas connect `CanX` / `CannotX` to the optimum bounds. See [the binary-answer example](examples/binary-search-answer.md).

Use this one business predicate when a complex, repeated extremum formula needs a problem name, avoiding expansion in every C invariant. When a direct library call is already clear, do not add a wrapper just to hide it.

### SumLib

For ordinary array/list segment sums, keep the annotation simple:

```c
ret == sum(sublist(0, i, l))
```

Indexed ranges, finite sets, and two-dimensional sums must reuse `sum_range` / `sum` / `sum_set_R` according to their signatures; use `Zrange` for enumeration and do not redefine these recursively. When a complex, repeated mathematical concept needs a name, retain one definition in `formal_case_lib` that calls these interfaces directly, avoiding expansion in every invariant.

`SumLib.SumLib` is the finite-set sum library's umbrella import. The example uses the existing `sum_range` from `SpecHelpers`, which also exports the required integer, list, and finite-set interfaces. The right endpoint for `[lo, hi)` is `hi - 1`. Use the expression directly in a result or accumulator equality, without a `RangeContribution` wrapper around that equality:

```coq
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Open Scope Z_scope.

Check (fun (l : list Z) (lo hi : Z) =>
  sum_range lo (hi - 1) (fun i : Z => Znth i l 0)).
```

Alternatively, use `SumLib.Sum.sum (fun i : Z => lo <= i < hi) (fun i => Znth i l 0)`; `SumLib.ZRange` supplies the `Finite` instance for this interval shape. `sum_set_R P f` requires `Finite P` and a real-valued `f`. The context must still supply valid domains for `Znth` reads. Use `AUXLib.ListLib.sum` for lists rather than accidentally selecting finite-set `sum P f` through a conflicting import.

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

### Reflexive-Transitive Closure of a Relation

Use `clos_refl_trans` for zero or more relation steps; do not recursively define `Reachable`, an execution chain, or a path `Inductive`. The current repository interface can be named explicitly:

```coq
Require Import Coq.ZArith.ZArith.
Require Import SetsClass.RelsDomain.

Check (fun (step : Z -> Z -> Prop) =>
  SetsClass.RelsDomain.clos_refl_trans step).
```

It includes the zero-step identity and any finite number of steps. A fixed number of relation compositions cannot replace it. Reuse type-compatible `valid_vpath` / `reachable` for graph-path semantics, and distinguish the repository closure from its standard-library namesake.

## Designing New Predicates and Invariants

When existing predicates are not enough, design the new predicate as a compact mathematical relation, not as an executable list program.

Predicate design rules:

- Avoid defining list properties with `Fixpoint` when a direct logical statement is clear. Prefer `forall` / `exists` over recursive traversal definitions.
- Use `Forall P l` for index-independent elementwise list facts instead of `forall i, 0 <= i < Zlength l -> P (Znth i l d)`. Use `Forall2` for corresponding elements of two lists.
- Use `Forall P (sublist lo hi l)` for elementwise facts on a valid segment. Retain guarded indexed quantification only for positions or relationships across indices; do not define a recursive list scanner.
- Select `Inductive` only within the output-type boundary in knowledge rules §1.4; proof convenience does not justify a new operation chain, reachability definition, or ordinary-value wrapper.
- Retain a predicate with multiple fields or a `Record` only for a clear mathematical concept. Do not use it to hide input ranges, capacities, safety conditions, or spatial ownership.
- Keep new predicates stable under small implementation changes. A good predicate describes the mathematical state, not the exact loop step that produced it.

Invariant writing rules:

- State only ranges needed downstream, directly in the annotation. Use `Forall` for index-independent elementwise constraints and guarded `forall` for positions or relationships across indices; reuse the established monotonicity library. Keep ranges and resources outside progress predicates.
- If the invariant selects one element, use `Znth i l d` directly.
- If the invariant selects a segment, use `sublist lo hi l` directly.
- Do not split a list only to expose one element, for example avoid shapes like `l == app(sublist(0, i, l), cons(a, sublist(i + 1, n, l)))` when `a == Znth i l d` states the same observation.
- Use `app` decomposition when the algorithm really maintains separately owned or separately permuted pieces, such as processed prefix and unprocessed suffix. Do not use it as a default way to read one value.
- Keep invariants readable. A smaller invariant usually produces smaller generated goals and gives Rocq less irrelevant structure to compile and prove through.

Preferred shapes:

```c
Forall(Z::le(lower), l) && Forall(Z::ge(upper), l)
cur == Znth(i, l, 0)
window == sublist(lo, hi, l)
```

Bubble sort gives a good inner-loop pattern:

```c
exists a,
  arr == arr@pre && n == n@pre &&
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
- Do extrema directly use `min_value_of_subset` / `max_value_of_subset` from `MaxMinLib`, including inside any necessary business predicate?
- Do sums, range enumeration, and closure reuse signature-compatible `sum_range` / `sum` / `sum_set_R`, `Zrange`, and `clos_refl_trans`?
- Is the new definition mathematical semantics, or is it copying the C loop?
- Are elementwise and corresponding-element relations expressed with `Forall` / `Forall2`, retaining indexed quantification only where position matters?
- Does each new predicate or `Record` contain only its target mathematics, without input ranges, execution-safety conditions, or resources?

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
