# Correct Example: Binary-Answer Annotation

This is a positive annotation example. For “binary search on an answer + a check predicate,” study the specification decomposition and invariant shape here before writing the current case's `formal_case_lib` and C annotations.

## Example files

Relevant files in this directory:

- `binary-search-annotation.md`: explains the positive pattern and how to design `CanX`, `CannotX`, and `OptimalX`.
- `split_array_largest_sum/binary-search-annotation.md`: a complete tutorial showing how the minimum-largest-segment-sum problem decomposes its specification, check function, and binary-search invariant.
- `split_array_largest_sum/split_array_largest_sum.c`: companion C annotations showing the organization of `Require`, `Ensure`, `Inv Assert`, and `where`.

Reuse only specification decomposition, predicate-first annotations, array-predicate choices, and loop-invariant shapes. Do not mechanically copy proof scripts, generated artifacts, or another case's formal files.

## Applicable pattern

The program usually has two layers:

- `check(arr, n, cap, ...)` scans the input and decides whether candidate answer `cap` is feasible.
- The main function binary-searches the answer space, narrows `[left, right]` according to `check(mid)`, and returns the least feasible answer.

The annotation must not restate the binary-search loop. It separates three kinds of mathematical fact:

- The prefix-scan state of `check`.
- The global property that says whether a candidate is feasible.
- The relationship that traps the true mathematical answer inside the current binary-search bounds.

## Recommended specification shape

Define business-semantics wrappers in `formal_case_lib` instead of expanding `MaxMinLib` in C annotations:

```coq
Definition CanSplit (l : list Z) (m cap : Z) : Prop := ...
Definition CannotSplit (l : list Z) (m cap : Z) : Prop := ...
Definition MinimizedMaxSegmentSum (l : list Z) (m ans : Z) : Prop := ...
```

To express “the least possible maximum among all legal solutions,” use `MaxMinLib`'s `min_value_of_subset` / `max_value_of_subset` inside those wrappers. The C annotations merely declare and call the wrappers:

```c
/*@ Extern Coq
      (CanSplit : list Z -> Z -> Z -> Prop)
      (CannotSplit : list Z -> Z -> Z -> Prop)
      (MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop)
 */
```

## The `check` function

The `Ensure` of `check` exposes only the decision property:

```c
Ensure
  (__return == 1 => CanSplit(l, m, cap)) &&
  (__return == 0 => CannotSplit(l, m, cap)) &&
  IntArray::full(arr, n, l)
```

Its loop uses a prefix-state predicate to connect local variables to mathematical meaning:

```c
Inv Assert
  0 <= i && i <= n@pre &&
  1 <= cnt && cnt <= i + 1 &&
  0 <= cur && cur <= cap@pre &&
  PrefixSplitState(l, cap@pre, i, cnt, cur) &&
  IntArray::full(arr, n@pre, l)
```

`PrefixSplitState` says that the segments formed while scanning prefix `i` satisfy the `cap` bound; it is not a Rocq version of the `check` program.

## Main loop

The main-loop invariant keeps the true answer inside the current bounds:

```c
Inv Assert
  exists ans,
    arr == arr@pre && n == n@pre && m == m@pre &&
    Zlength(l) == n@pre &&
    IntArray::full(arr, n@pre, l) &&
    0 <= left && left <= right && right <= 1000000000 &&
    left <= ans && ans <= right &&
    MinimizedMaxSegmentSum(l, m, ans)
```

Here `ans` is a mathematical answer, not a program variable. Loop preservation needs only these implications:

- `CanSplit(l, m, mid)` implies `ans <= mid`, permitting `right = mid`.
- `CannotSplit(l, m, mid)` implies `mid < ans`, permitting `left = mid + 1`.

Prove these connections as proof-side helper lemmas. The annotation retains only the premises required to apply them.

## Checklist

- Does the return value of `check` expose a `CanX` / `CannotX` decision property?
- Does the main problem use a `Minimized...`, `Maximized...`, or equivalent mathematical wrapper?
- Does the main-loop invariant state that the true answer lies in `[left, right]`?
- Do the `ok` branches retain the feasible/infeasible fact, `mid` range, and boundary facts?
- Do the C annotations describe mathematical state instead of tracking a Rocq binary-search program?

## How to use this example

For binary search on an answer, feasibility decisions, minimax/maximin optimization, or a `check` helper:

1. Read this file and decide whether the current case has the same algorithmic shape.
2. Read `split_array_largest_sum/binary-search-annotation.md` to learn how to separate `check`'s prefix state, candidate feasibility, and true-answer bounds.
3. Inspect the C annotations in `split_array_largest_sum/split_array_largest_sum.c`, focusing on function specifications, the main-loop invariant, the `check` invariant, and pure facts retained at calls.

The essential criteria are:

- The specification first expresses mathematical semantics through `formal_case_lib` wrappers.
- `check` exposes only feasible/infeasible decisions.
- The main-loop invariant keeps the true answer inside the current `[left, right]`.
- Proof-side bridge lemmas do not belong in C annotations. A group worker proves a helper bearing the current group suffix, or the annotation round promotes a necessary mathematical definition to a seed declaration.
