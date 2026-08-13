# `split_array_largest_sum`: Binary-Search Tutorial

This directory contains a positive annotation example for `split_array_largest_sum`, intended to guide agents proving “binary search on an answer + a check predicate” directly. The companion C example is:

- `split_array_largest_sum.c`
- Formal C source: `QCP_examples/LLM_bench/Algorithms/split_array_largest_sum/split_array_largest_sum.c`
- Formal definitions: `Rocq/examples/LLM_bench/Algorithms/split_array_largest_sum/split_array_largest_sum_lib.v`

For a similar case, learn the specification decomposition and invariant shapes here. Do not treat this as a proof script to copy mechanically.

## Applicable pattern

This example covers programs with the following shape:

1. The main function binary-searches the answer space.
2. A helper `check` function decides whether a candidate `cap` is feasible.
3. The return value of `check` is monotone: if a `cap` is feasible, larger candidates are feasible; if it is infeasible, smaller candidates are infeasible.
4. The main loop narrows `[left, right]` using `check(mid)` and ultimately returns the least feasible answer.

The annotation should not restate the binary-search code. It separates three mathematical layers:

- The prefix decision state maintained by `check`.
- The global property saying whether candidate `cap` is feasible.
- The relationship between the true answer and the current binary-search bounds.

## Why these predicates are used

### `PrefixSplitState`

`check` scans the array and maintains:

- Processed-prefix length `i`.
- Number of segments used so far, `cnt`.
- Sum of the current segment, `cur`.
- The fact that every completed segment is at most `cap`.

`PrefixSplitState(l, cap, i, cnt, cur)` is not a Rocq version of the `check` program. It is the mathematical state formed after scanning prefix `i`. The C loop invariant binds local variables to this property:

```c
0 <= i && i <= n@pre &&
1 <= cnt && cnt <= i + 1 &&
0 <= cur && cur <= cap@pre &&
PrefixSplitState(l, cap@pre, i, cnt, cur)
```

Each loop step then proves only that consuming one more element preserves the prefix property, rather than proving that C and a recursive Rocq interpreter advance in lockstep.

### `CanSplit` / `CannotSplit`

The external specification of `check` must not expose internal scan details. It only tells the caller:

- On return `1`, `cap` is large enough to split the list into at most `m` segments.
- On return `0`, `cap` is too small for such a split.

The corresponding annotation is:

```c
(__return == 1 => CanSplit(l, m, cap)) &&
(__return == 0 => CannotSplit(l, m, cap))
```

This lets the main loop turn the result of `check(mid)` into a boundary update. The internal `check` invariant proves `PrefixSplitState`, and the function `Ensure` packages that state as `CanSplit` / `CannotSplit`.

### `PartitionMaxSegmentSum` / `MinimizedMaxSegmentSum`

The main function's true obligation is: “the return value is the least possible maximum segment sum among all legal partitions.” Express this first as a strictly mathematical definition, instead of defining a Rocq `splitArrayLargestSum` program and proving that C agrees with it.

The example uses the mathematical interface from `MaxMinLib`:

- `MaxSegmentSum` uses `max_value_of_subset` for the largest segment sum of one partition.
- `PartitionMaxSegmentSum` describes a legal partition of length `m` and its maximum segment sum.
- `MinimizedMaxSegmentSum` uses `min_value_of_subset` for the least maximum segment sum among all legal partitions.

Together these definitions give the mathematical semantics of the problem. The C program must satisfy those semantics, not agree with another program.

## Main binary-search invariant

The key invariant is:

```c
exists res,
arr == arr@pre && n == n@pre && m == m@pre &&
1 <= n@pre && n@pre <= 100000 &&
1 <= m@pre && m@pre <= n@pre &&
Zlength(l) == n@pre &&
IntArray::full(arr, n@pre, l) &&
(forall (i : Z), (0 <= i && i < n@pre) => (0 <= l[i] && l[i] < 100000000)) &&
0 <= left && right <= 1000000000 &&
left <= right &&
left <= res && res <= right &&
MinimizedMaxSegmentSum(l, m, res)
```

Here `res` is the mathematical answer, not a program variable. This existential is the central bridge for the binary-search loop:

- At initialization, the function `Require` provides an `ans` satisfying `MinimizedMaxSegmentSum(l, m, ans)` and `0 <= ans <= 1000000000`.
- During preservation, `res` continues to represent the same mathematical answer; the proof only shows that the updated bounds still satisfy `left <= res <= right`.
- At exit, `left == right` together with `left <= res <= right` shows that the return value is exactly `res`, and hence satisfies `MinimizedMaxSegmentSum(l, m, __return)`.

Do not write an invariant containing a Rocq state machine for how many binary-search iterations have occurred or how the next `mid` is computed. The mathematical fact to maintain is that the current bounds trap the answer.

## Connecting `check` to the binary-search bounds

The result of `check(mid)` says only whether candidate `mid` is feasible. The main loop also needs helper lemmas connecting it to optimal answer `res`:

- `CanSplit(l, m, mid)` and `MinimizedMaxSegmentSum(l, m, res)` imply `res <= mid`. Thus, when `ok == 1`, set `right = mid`.
- `CannotSplit(l, m, mid)` and `MinimizedMaxSegmentSum(l, m, res)` imply `mid < res`. Thus, when `ok == 0`, set `left = mid + 1`.

In the current `formal_case_lib` or a later `group_worker_lib`, lemmas similar to the following provide these connections:

- `minmax_can_lower_bound`
- `minmax_cannot_upper_bound`
- `partition_max_to_can_split`
- `can_split_to_partition_max`

Do not insert these proofs into C assertions. The annotations retain enough pure facts and spatial resources for the VC to apply the lemmas:

- `MinimizedMaxSegmentSum(l, m, res)`.
- `CanSplit(l, m, mid)` or `CannotSplit(l, m, mid)`.
- `1 <= m <= Zlength l`.
- Nonnegativity of elements.
- `left <= res <= right`.
- The range and integer bounds for `mid`.

## What not to do in Rocq

Do not take this route:

1. Define a recursive function or state machine in Rocq to simulate `check`.
2. Define another recursive function to simulate the main binary-search loop.
3. Track the results of those functions in the C annotations.
4. Prove step-by-step agreement between the C and Rocq programs.

That changes the goal from “the C program satisfies the mathematical minimum-largest-segment-sum property” into “two programs agree.” It also makes every small control-flow or annotation change invalidate the entire mirrored Rocq algorithm.

The correct route is:

- Describe the target property first with strict mathematical definitions.
- Use a prefix state in `check` to prove its decision property.
- Use a boundary invariant in the main loop to keep the mathematical answer trapped.
- Put only necessary connection proofs in helper lemmas. If a connection is a proof-side bridge, a group worker adds a helper with its current group suffix to `group_worker_lib`, which vc-proving later merges after parent verification.

## Checklist before writing a similar case

1. Is the return value of `check` packaged as a `CanX` / `CannotX` decision property?
2. Is the main problem expressed using `min_value_of_subset`, `max_value_of_subset`, or an equally mathematical definition?
3. Does the main-loop invariant say that the true answer lies inside `[left, right]`?
4. Do the `ok` branches have lemmas converting feasible/infeasible results into `res <= mid` or `mid < res`?
5. Do the C annotations describe program state rather than track a Rocq program?

If item 5 fails, return to predicate-first design before entering vc-proving.
