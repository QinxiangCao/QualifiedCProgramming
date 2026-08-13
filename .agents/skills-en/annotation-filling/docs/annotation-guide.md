# Annotation Rules, Persistent Sessions, and In-Turn Repair

This document is for the annotation subagent. Its goal is to repair the C annotations and `formal_case_lib` specification declarations in the main root until they are ready for `annotation-checking` and the main-owned `annotation-check-round`.

## Allowed modifications

You may modify only:

- `Require` / `Ensure` clauses in the target `.c` file.
- `Assert` clauses required to advance verification.
- Loop `Inv Assert` clauses.
- Function-call `where` clauses.
- Mathematical specification declarations in the `formal_case_lib` at the same formal relative path.

Do not manually edit `*_goal.v`, `*_proof_auto.v`, `*_proof_manual.v`, or `*_goal_check.v`, and do not create a second active Rocq library.

## Specification first

First define the mathematical problem itself in `formal_case_lib`; then make the C annotations explain how the program maintains and implements those properties.

If the current `formal_case_lib` contains only the controller's minimal import seed, design the specification there in the current turn. Do not return blocked because “there is no existing library” or “the specification direction needs user confirmation.” If the handoff's problem context is empty, infer a conservative candidate specification from the C function names, parameters, return values, loop structure, and problem directory.

Suitable `formal_case_lib` declarations include `subarray_sum`, `prefix_sum`, `suffix_sum`, sortedness/permutation, reachability, queue coverage, DP-table meaning, string-matching relations, and optimality or feasibility relations.

Do not directly write a Rocq version of the C loop body or a complete C state machine. A quick test is: could this definition explain the correctness of a different implementation? If not, it is usually not an appropriate specification.

Functional cases such as sorting, deduplication, searching, optimization, graph search, and dynamic programming must establish mathematical result semantics on the first iteration. Shape, bounds, and ownership are execution conditions, not a functional specification.

### Predicate-first design order

For each function, answer three questions before writing annotations:

1. Which mathematical input/output relationship must `Ensure` prove?
2. Which hidden local property does each loop maintain at the current program point?
3. Should those properties be expressed by an existing predicate, a case-level wrapper, or a new `formal_case_lib` declaration?

A hidden property is a mathematical fact actually preserved in program state, not the same code rewritten in Rocq syntax. Typical forms include:

- Processed prefix / unprocessed suffix.
- Merged prefix / pending left and right intervals.
- Current candidate maximum, minimum, optimum, or feasibility boundary.
- Written prefix plus uninitialized suffix.
- Current abstract queue, graph reachability, or DP-table meaning.
- Permutation, sortedness, bounds, preserved shape, and segment ownership.

If a new definition begins to reproduce loop locals and step transitions one-for-one, stop and return to predicate-first design. Read `docs/incorrect-examples/algorithm-mirror.md`, then inspect the `max_sub_array` counterexample files.

### Choosing `formal_case_lib` declarations

Prefer short, stable, reusable mathematical interfaces:

- For a sorting result, combine `Permutation` with `increasing` / `decreasing`.
- For a segment sum, use `sum(sublist lo hi l)` directly in ordinary cases; wrap `SumLib` in a business predicate for complicated indexed sums.
- For maxima, minima, and optima, wrap `MaxMinLib` in a `Minimized...`, `Maximized...`, or `Optimal...` predicate.
- For binary search on an answer, define `CanX`, `CannotX`, and the true-answer predicate. The main-loop invariant keeps the answer inside the current bounds. Read `docs/correct-examples/binary-search-annotation.md`; the companion C annotations are in `docs/correct-examples/split_array_largest_sum/`.
- For dynamic programming, define the mathematical meaning of a table entry rather than defining another recursive DP program and tracking it.
- For a refinement proof, retain only the `safeExec` / monadic specification required by the proof type; do not duplicate final functional correctness inside the C loop invariant.

A preferred new declaration has the shape:

```coq
Definition BusinessPredicate (l : list Z) (args : Z) : Prop := ...
```

Prefer `forall` / `exists`, `Znth`, `Zlength`, `sublist`, `Permutation`, `sum`, and case-level wrappers. Introduce an `Inductive` only when the inductive structure itself is the business semantics. Do not write a `Fixpoint` merely to simulate a program loop.

## Annotation style

Use “complete at key points, minimal for ordinary steps”:

- Write complete `Assert` / `Inv Assert` clauses at function entry/exit, loop invariants, important branch joins, before and after calls, and around expressions that change abstract state.
- Do not mechanically insert a full assertion after ordinary sequential statements, single assignments, or local transformations symbolic execution can advance automatically.
- In loops, maintain the processed prefix/suffix, pending interval, current candidate optimum, abstract state, local shape, written prefix, and unwritten suffix as appropriate.
- When entry-state values are needed, explicitly preserve bridge equalities from current variables to `@pre` variables.
- Before a call, confirm that every list, length, and value-level fact required by `where` / `With` is present in the current assertion.

When the C type or local store already entails a pure fact but the witness does not expose it, materialize the value and use a lightweight annotation:

```c
unsigned int __u = u;
/*@ 0 <= u && u <= UINT_MAX by local */
```

`by local` exports only the pure fact; it does not retain spatial resources.

### Assertion-placement rules

A complete `Assert` / `Inv Assert` should cover:

- The live local store, or equivalent resources that let QCP reclaim local permissions.
- Currently owned heap, array, string, and shape resources.
- Bridge equalities among abstract lists, segments, prefixes/suffixes, and program variables.
- `@pre` parameter bridges such as `n == n@pre` and `arr == arr@pre`.
- Bounds, branch conditions, loop guards, and array-read bindings.
- The current hidden property or business predicate.

Do not blanket every assignment with a full assertion. Let symbolic execution advance ordinary one-step transformations. Use a complete assertion only when resource shape or abstract state changes, at a branch join, around a function call, at a loop boundary, or when QCP cannot discover a key pure fact automatically.

### Loop-invariant shape

Start a loop invariant with “progress + resources + mathematical state”:

```c
Inv Assert
  exists done todo state,
    l == app(done, todo) &&
    i == Zlength(done) &&
    0 <= i && i <= n@pre &&
    LoopStatePredicate(done, state) &&
    IntArray::full(a, n@pre, l)
```

Common array-scan shapes:

- Read-only scan: `IntArray::full(a, n, l)` + `i == Zlength(done)` + `l == app(done, todo)`.
- In-place update: `new_l == replace_Znth(i, v, old_l)`, retaining the restored `full` resource.
- Multi-cursor intervals: prefer several `seg` resources for `[lo, mid)`, `[mid, hi)`, and similar logical parts.
- Incrementally written uninitialized buffer: written-prefix `seg` / `seg_shape` plus unwritten-suffix `undef_seg`.
- Binary search on an answer: maintain the mathematical answer `ans` inside `[left, right]`; do not maintain a “binary-loop executor.”

Use an `app` decomposition only when the prefix, selected element, and suffix have independent algorithmic meaning. If the code merely observes one index, `Znth(i, l, default)` plus bounds is clearer.

## Common errors

- Missing `@pre` bridge: the postcondition uses an entry value, but assertions preserve only the current value.
- Missing binding after an array read: if later reasoning needs the logical-list value, write `val == l[i]` together with bounds and the array resource.
- Using tautologies such as `x == x` or `p == p` to pretend a variable was preserved. Replace them with `x == x@pre`, `local == logical_value`, or `new_l == replace_Znth(...)`.
- In a refinement case, putting final functional correctness inside the C invariant. C annotations should expose the resources, local values, branch facts, bounds, and current `safeExec` state needed for simulation.
- An invariant that is too strong to initialize or preserve, or too weak to imply `Ensure` at exit.
- A full assertion that loses the live local store, an array segment, or a shape resource.
- A `where` clause that supplies only a pointer but not the list, length, or value-level facts needed to instantiate the callee specification.
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

## Self-repair loop

The following failures are self-reworkable by default:

- `spec-quality`
- `qcp-symbolic-execution`
- `where-instantiation`
- `formal_case_lib-coqc`
- `annotation-checking-failed`
- `invariant-too-weak`
- `invariant-too-strong`
- `resource-loss`

On each turn, the one annotation agent follows at least this loop until the candidate is ready, stale, compact-error, or a required tool has a major failure:

1. `design`: list the mathematical result semantics that each function's `Ensure` must express.
2. `local-static-review`: check live resources, `@pre` bridges, bindings from locals to array values, and logical properties needed at loop exit.
3. `formal_case_lib-check`: run the handoff's `controller.py coq-check --target-kind formal-case-lib` command exactly as rendered against the main-root `formal_case_lib`. Do not invoke the internal helper or write the target/build path yourself.
4. `qcp-check`: check the target `.c` using the handoff driver that accepts the canonical `-I` / `-slp` arguments.
5. `annotation-checking`: turn a failed result into a concise repair plan for the next check in this turn, written to the current `agent_output.md`.
6. `repair`: repair one coherent class of issues, then begin the next check cycle.

Default budget: at least three complete `design/check/repair` cycles, or at least 30 minutes of actual annotation work. Use `stale` if the input version changes. For context compaction, record only the `compact-error` fact; place reusable hints in this attempt's `agent_output.md`. The controller/main agent decides whether to append another task or ultimately block, and compaction never permits a second annotation agent. Return `blocked` only when the controller's canonical symbolic execution, the formal-case-lib `coq-check`, or a script required by annotation-checking is completely unusable and command evidence exists. A missing specification, temporary `formal_case_lib` compilation failure, QCP failure, failed `where` instantiation, failed annotation-checking, inferred problem semantics, or missing reference hint must instead be repaired in this turn or result in a concrete candidate.

If the controller handoff explicitly sets `consider_broader_refactor: true`, first reevaluate the specification's
abstraction level and direction. Then inspect the connections among function postconditions, loop invariants, local
assertions, and call `where` clauses together. Consider deleting and rewriting an incorrect annotation structure
instead of assuming the first two annotation-causal repairs' local-patch direction remains valid. This requirement
comes from the controller's causal count, not the annotation-directory ordinal.

## Analyzing QCP failures

For every canonical QCP failure, record briefly in `agent_output.md`:

- The `first_failure` category and message, plus the failing file/line/function. Do not repeat command, cwd, target, or canonical flags already present in the handoff/controller.
- The nearest `Require`, `Ensure`, `Assert`, `Inv Assert`, or `where`.
- A summary of symbolic state, especially array/list/shape resources.
- The failure class: pure fact, resource shape, specification mismatch, loop invariant, call instantiation, or `formal_case_lib` mismatch.
- The next repair.

Do not change one line and immediately rerun QCP. Classify the failure first, then repair a coherent set of related issues.

## Output

The current `agent_report.json` contains only the terminal status, exact changed files relative to this attempt's before history, three check statuses, and blockers. Put iterations, failure classifications, repair actions, branch decisions, and residual risks in the current `agent_output.md`; do not duplicate JSON evidence for every cycle. `finalize-delivery` mechanically preflights this report before returned status/after history. If it returns `report-repair-required`, the same owner repairs it in the same running delivery and reruns the original command without creating a new attempt. Only after preflight does the controller archive the current files; the agent does not write history. Before `completed`, canonical QCP, the `formal_case_lib` check, and annotation-checking must all pass. Main-owned clean-output replay and final-check then validate generation freshness independently.
