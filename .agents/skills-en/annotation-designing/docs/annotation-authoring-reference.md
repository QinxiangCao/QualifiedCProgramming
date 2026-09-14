# QCP C Annotation Authoring Reference

This file preserves QCP-language, resource-shape, loop-invariant, and failure-analysis details. The workflow is authoritative for stage order, commands, and reports.

This document is for the single annotation owner. Its goal is to revise specifications, C annotations, and `formal_case_lib` declarations together in the main root until they are ready for the main-owned `annotation-check-round`.

## Allowed modifications

You may modify only:

- Specifications, genuinely needed ordinary `Assert` clauses, and an `Inv Assert` before every loop in the target `.c` file.
- Mathematical specification declarations in the `formal_case_lib` at the same formal relative path.

Do not add `by local`, branch control, ordinary `Inv`, multi-invariants, or call `where` clauses in function bodies.

Do not manually edit `*_goal.v`, `*_proof_auto.v`, `*_proof_manual.v`, or `*_goal_check.v`, and do not create a second active Rocq library.

## Specification first

First derive natural-language `Signature`, `Preconditions`, and `Output` from the problem. Then write equivalent Rocq `Pre` / `Spec`, followed by C function contracts and loop invariants that use those properties.

Use the problem statement, input/output formats, and sample notes needed to remove ambiguity as specification sources. Use C only to identify parameters, resources, and helper call relationships. If the current `formal_case_lib` contains only the minimal import seed, write the Rocq form of the natural-language specification there. The annotation owner may revise a specification not supplied by the user in the current attempt. Preserve a user-provided specification; if it needs a change, stop, write the proposal in `agent_output.md`, and continue after user approval and `unfreeze`.

Before adding a declaration, search for existing `sublist`, `sum`, `Permutation`, monotonicity, extrema, `reachable`, and other core interfaces. Add only an independent, repeated mathematical property from the problem, a helper, or a loop to `formal_case_lib`.

Write combinations of core interfaces directly in a specification or invariant instead of defining forwarding wrappers. When a problem output or cross-function interface needs one name, keep one case predicate and make helpers and loops refer to that layer.

Do not directly write a Rocq version of the C loop body or a complete C state machine. A quick test is: could this definition explain the correctness of a different implementation? If not, it is usually not an appropriate specification.

Functional cases such as sorting, deduplication, searching, optimization, graph search, and dynamic programming must establish mathematical result semantics on the first iteration. Shape, bounds, and ownership are execution conditions, not a functional specification.

### Specification and Predicate-Reuse Order

For each function, answer three questions before writing annotations:

1. What are the natural-language `Output` and Rocq `Spec`?
2. How does `Ensure` connect directly to that input/output relation?
3. What one sentence of mathematical progress does each loop maintain?
4. Can existing predicates express it directly? If not, which repeated property genuinely needs a new declaration?

A hidden property is a mathematical fact actually preserved in program state, not the same code rewritten in Rocq syntax. Typical forms include:

- Processed prefix / unprocessed suffix.
- Merged prefix / pending left and right intervals.
- Current candidate maximum, minimum, optimum, or feasibility boundary.
- Written prefix plus uninitialized suffix.
- Current abstract queue, graph reachability, or DP-table meaning.
- Permutation, sortedness, bounds, preserved shape, and segment ownership.

If a new definition begins to reproduce loop locals and step transitions one-for-one, replace it with the mathematical property maintained by the loop. Read [the algorithm-mirror counterexample](examples/algorithm-mirror.md) when needed.

### Choosing `formal_case_lib` declarations

Prefer short, stable, reusable mathematical interfaces:

- For a sorting result, combine `Permutation` with `increasing` / `decreasing`.
- For a segment sum, use `sum(sublist lo hi l)` directly in ordinary cases; wrap `SumLib` in a business predicate for complicated indexed sums.
- For maxima, minima, and optima, prefer `min_value_of_subset`, `max_value_of_subset`, or another interface already present in the dependencies. Retain one business name only when the problem concept is reused.
- For binary search on an answer, define `CanX`, `CannotX`, and the true-answer predicate. The main-loop invariant keeps the answer inside the current bounds. Read [the binary-answer example](examples/binary-search-answer.md); the companion C annotation is `examples/split_array_largest_sum.c`.
- For dynamic programming, define the mathematical meaning of a table entry rather than defining another recursive DP program and tracking it.
- For a refinement proof, retain only the `safeExec` / monadic specification required by the proof type; do not duplicate final functional correctness inside the C loop invariant.

A preferred new declaration has the shape:

```coq
Definition BusinessPredicate (l : list Z) (args : Z) : Prop := ...
```

Prefer `forall` / `exists`, `Znth`, `Zlength`, `sublist`, `Permutation`, `sum`, and existing core predicates. Add one case predicate only when a problem or interface needs a name. Introduce an `Inductive` only when the inductive structure itself is the business semantics. Do not write a `Fixpoint` merely to simulate a program loop.

That one case predicate names problem mathematics and does not sit behind another synonymous layer. Expand function-specification input sizes, scalar/element ranges, and overflow/safety conditions directly; never define or call wrapper predicates such as `SizeSafe`, `InputValues`, `InputValid`, or `InputBound` for them.

## Annotation style

Use “complete loop invariants, minimal everywhere else”:

- Put an `Inv Assert` before every loop, maintaining processed/unprocessed portions, the current candidate state, and live resources.
- Do not put an ordinary `Assert` immediately before an `Inv Assert`.
- An ordinary `Assert` may appear before an `if` when needed and never before a `return`; elsewhere, add one only when symbolic execution genuinely cannot determine state required by verification.
- Do not add assertions around ordinary sequential statements, single assignments, or local transformations symbolic execution can advance automatically.
- Write `n == n@pre` if and only if `n` has not changed in value from function entry to the current point; never write it for a changed value. After the bridge, use current `n` for every other fact in the same assertion.

### Assertion-placement rules

A complete `Assert` / `Inv Assert` should cover:

- The live local store, or equivalent resources that let QCP reclaim local permissions.
- Currently owned heap, array, string, and shape resources.
- Bridge equalities among abstract lists, segments, prefixes/suffixes, and program variables.
- `@pre` bridges used if and only if the parameter value is unchanged.
- Bounds, branch conditions, loop guards, and array-read bindings.
- The current hidden property or business predicate.

Do not blanket assignments with assertions. Let symbolic execution advance ordinary one-step transformations, and use ordinary `Assert` only at the limited locations above.

### Loop-invariant shape

Start a loop invariant with “progress + resources + mathematical state”:

```c
Inv Assert
  exists done todo state,
    n == n@pre &&
    l == app(done, todo) &&
    i == Zlength(done) &&
    0 <= i && i <= n &&
    LoopStatePredicate(done, state) &&
    IntArray::full(a, n, l)
```

`IntArray::full(a, n, l)` already includes `Zlength(l) == n` and `0 <= n`; resources such as `IntArray::seg` likewise include their own length and interval facts. Do not repeat those facts in the same annotation. Keep an access bound such as `0 <= i < n` when the actual array access needs it.

Common array-scan shapes:

- Read-only scan: `IntArray::full(a, n, l)` + `i == Zlength(done)` + `l == app(done, todo)`.
- In-place update: `new_l == replace_Znth(i, v, old_l)`, retaining the restored `full` resource.
- Multi-cursor intervals: prefer several `seg` resources for `[lo, mid)`, `[mid, hi)`, and similar logical parts.
- Incrementally written uninitialized buffer: written-prefix `seg` / `seg_shape` plus unwritten-suffix `undef_seg`.
- Binary search on an answer: maintain the mathematical answer `ans` inside `[left, right]`; do not maintain a “binary-loop executor.”

Use an `app` decomposition only when the prefix, selected element, and suffix have independent algorithmic meaning. If the code merely observes one index, `Znth(i, l, default)` plus bounds is clearer.

## Common errors

- An unchanged variable that must be recorded lacks a bridge such as `n == n@pre`; a changed variable incorrectly has that bridge; or ranges/resources still use `n@pre` instead of current `n` after the bridge.
- Missing binding after an array read: if later reasoning needs the logical-list value, write `val == l[i]` together with bounds and the array resource.
- Using tautologies such as `x == x` or `p == p` to pretend a variable was preserved. Keep only a needed `local == logical_value`, `new_l == replace_Znth(...)`, or genuine entry-value relation.
- In a refinement case, putting final functional correctness inside the C invariant. C annotations should expose the resources, local values, branch facts, bounds, and current `safeExec` state needed for simulation.
- An invariant that is too strong to initialize or preserve, or too weak to imply `Ensure` at exit.
- A full assertion that loses the live local store, an array segment, or a shape resource.
- Treating a local value read from an array as an unconstrained integer instead of recording `v == Znth(i, l, 0)` or the case's equivalent observation.
- Replacing business semantics with a proof-facing predicate—for example, replacing `increasing(l)` with many `mono_*` facts merely for proof convenience.
- Expanding `MaxMinLib` / `SumLib` details in C annotations so that each invariant repeats a complex finite-set formula.
- Adding an unsound shortcut, `Axiom`, or a definition that reuses a seed declaration's name with different contents in `formal_case_lib`.

Repair these errors in the main root; do not force the manual VC proof to compensate for them.

### Deciding when to return to annotations

These proof-side failures usually require an annotation repair:

- The VC premises omit an array-read binding, loop guard, branch fact, or `@pre` bridge.
- The `safeExec` abstract state does not match the goal, and a simple unfold / `prog_nf` does not resolve it.
- A helper lemma requires a business premise absent from the invariant or `Ensure`.
- `Ensure` states only shape or bounds and omits the function's true functional specification.

These failures usually do not require annotation repair:

- The semantic predicate is exposed correctly but a bridge lemma is missing.
- List arithmetic or a connection involving `sublist`, `replace_Znth`, `Permutation`, or `MaxMinLib` needs a proof.
- A worker needs a new helper bearing the current group suffix.

## Staged self-repair loop

The following failures remain repairable by the same owner by default:

- `spec-quality`
- `qcp-symbolic-execution`
- `where-instantiation`
- `formal_case_lib-coqc`
- `annotation-design-plan`
- `invariant-too-weak`
- `invariant-too-strong`
- `resource-loss`

The one annotation owner follows the current stage until completed, stale, compact-error, or a genuine blocker:

1. Design the natural-language specification, Rocq specification, function contracts, necessary predicates, C annotations, case-library lemmas, and concise plan in order.
2. Run the handed-off design-library check, canonical symexec, and applicable post-symexec library check.
3. Repair the specification, invariant, resource, or lemma corresponding to the first failed VC; continue while the gap remains.

If the controller handoff explicitly sets `consider_broader_refactor: true`, first reevaluate the specification's
abstraction level and direction. Then inspect the connections among function postconditions, loop invariants, local
assertions together. Consider deleting and rewriting an incorrect annotation structure
instead of assuming the first two annotation-causal repairs' local-patch direction remains valid. This requirement
comes from the controller's causal count, not the annotation-directory ordinal.

## Analyzing QCP failures

For every canonical QCP failure, record briefly in `agent_output.md`:

- The `first_failure` category and message, plus the failing file/line/function. Do not repeat command, cwd, target, or canonical flags already present in the handoff/controller.
- The nearest `Require`, `Ensure`, `Assert`, or `Inv Assert`.
- A summary of symbolic state, especially array/list/shape resources.
- The failure class: pure fact, resource shape, specification mismatch, loop invariant, call instantiation, or `formal_case_lib` mismatch.
- The next repair.

Do not change one line and immediately rerun QCP. Classify the failure first, then repair a coherent set of related issues.

## Output

On success, the current `agent_report.json` contains only `{"status":"completed"}`; a blocked report adds only the workflow's complete blocker. Put iterations, failure classifications, design decisions, branch decisions, and residual risks in `agent_output.md`. If `finalize-delivery` returns `report-repair-required`, the same owner follows its message in the same attempt and reruns the original command. A user-specification proposal goes only in `agent_output.md` and does not run `finalize-delivery`. Before completion, the design-library check, canonical QCP, VC comparisons, and applicable post-symexec library check must pass.
