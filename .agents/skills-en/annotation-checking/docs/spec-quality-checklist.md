# Specification Quality Checklist

The purpose of this check is not to prove every VC. It is to catch clearly incorrect C annotations and `formal_case_lib` content before `annotation-check-round`.

## `formal_case_lib`

For every external Rocq predicate, function, or relation used in the C annotations, confirm that:

- Its declaration exists and its name, arity, and parameter order match the C annotations.
- The handoff command `controller.py coq-check --target-kind formal-case-lib` passes. The agent must not invoke the internal helper directly or assemble the target/build path itself.
- Its contents are a mathematical specification, not a reproduction of the current C program's control flow.
- The definition could establish the correctness of another reasonable implementation rather than explaining only this implementation's loop locals and step transition.
- It is strong enough to derive the result semantics in the function's `Ensure`, without making one implementation strategy the only permitted behavior.
- It contains no `Admitted.`, extra `Axiom`, or `SimpleC.EE.*` import of a generated artifact for the current case.

If a definition is missing, points in the wrong direction, or its evidence refers to the wrong path, return `failed` and require a repair in `annotation-filling`.

Direct proofs use predicate-first annotations by default. An obvious algorithm-mirror `Fixpoint` or state machine requires `failed`. A refinement proof may retain the `safeExec` / monadic specification required by its proof type, but prefixes, suffixes, processed intervals, candidate optima, and other local runtime properties must still appear directly in the C annotations. See `../annotation-filling/docs/predicate-first-annotation.md`.

### Lightweight review of higher-order existential witnesses

Perform this review only when the specification contains `exists f : A -> B, ...` or an equivalent higher-order function witness; it does not apply to other existential quantifiers. Record the following in the current `agent_output.md`:

```text
higher_order_witness_review:
  domain:
  finite_contiguous_domain: yes | no
  uniquely_determined_by_input: yes | no
  canonical_definition_available: yes | no
  finite_sequence_representation_available: yes | no
  selected_representation: canonical-value | list | existential-function
  justification:
```

- Prefer a transparent canonical value when the result is uniquely determined and has a clear mathematical closed form.
- For a sequence over a finite contiguous domain, prefer a length-constrained list when later proofs mainly use length, indexing, prefixes/suffixes, and segmentation.
- Retain an existential function when the mathematical object is inherently a mapping or a functional interface materially simplifies the proof.
- Do not automatically reject `exists f` or equate it with a choice axiom. If it is retained, explain its domain, valid range, and concrete advantage over a canonical value or list.
- Canonical definitions and list profiles must still describe mathematical objects, not mirror the C algorithm or loop body.
- If a transparent constructor or construction lemma already exists, do not leave repeated search for the same function witness to proof workers.

## Function-specification checks

A function specification must distinguish at least three categories of facts:

- Execution facts: integer ranges, index ranges, loop bounds, and overflow limits.
- Memory facts: arrays, lists, structures, pointers, and owned resources.
- Logical properties: what the function computes mathematically.

The third category must answer “what does the result mean?” For example, sorting requires sortedness and permutation, searching requires found/not-found semantics, and optimization requires feasibility, optimality, or an extremum definition. A specification containing only shape, bounds, and a return-value range is usually insufficient.

For a `check` or helper function, also verify that its `Ensure` exposes the decision property required by its caller. A return range such as `0 <= ret <= 1` without a connection between `ret` and feasible/infeasible semantics cannot pass.

### Array/string memory-predicate checks

For arrays, character buffers, C strings, or string literals, consult `../annotation-filling/docs/array-string-guide.md`:

- Prefer existing array families such as `IntArray`, `UIntArray`, `CharArray`, and `PtrArray`, together with `store_string`, `store_stringLit`, and `GlobalStrings`.
- Use `store_string` only for a writable C-string buffer; its logical contents are a `list Z` without the trailing zero.
- Use `store_stringLit` only for a string literal or read-only global string constant; its logical contents are a Rocq `string`.
- Do not describe a local `char a[] = "..."` or another writable buffer with `store_stringLit`.
- If `formal_case_lib` adds an array/string memory predicate, first determine whether it duplicates a builtin. The case library should add mathematical properties of the algorithm, not duplicate foundational memory semantics.

## Loop-invariant checks

A loop invariant must include at least:

- Variable ranges, index relationships, and integer-overflow limits.
- The currently owned array, list, buffer, or other memory resources.
- The mathematical relationship between the processed portion and the overall goal.

Common failures include having only bounds and array resources, referring directly to a Rocq version of the loop function, being unable to derive the `Ensure` at exit, failing initialization or preservation, or omitting `@pre` bridges, local-variable bindings, or live local resources from a full assertion.

## Semantic review of ordinary `Assert`

Check primarily that `Inv Assert` carries the mathematical loop state; retain an ordinary `Assert` only for its connection role. If any ordinary `Assert` exists, review each one under `../annotation-filling/docs/semantic-assert-placement.md`. If none exists, record `none` in the current `agent_output.md`.

For every ordinary `Assert`, record at least:

```text
location:
purpose: one or more of function-call-boundary | semantic-phase-transition | path-join | exit-bridge
named_semantic_state: predicate name | none
upstream_paths: qualitative description
downstream_work: qualitative description
redundant_with_invariant_or_postcondition: yes | no
decision: keep | remove | revise
rationale:
```

Path analysis is qualitative; it does not require exact enumeration or a formal audit of every path. The key question is whether the assertion collapses several concrete symbolic states into a stable domain property that downstream work actually uses.

Prefer to remove or revise:

- An assertion at the loop-body entry that copies the invariant and adds only the loop guard.
- A branch-end assertion immediately before the back edge that merely restates the next-iteration invariant.
- An assertion after a simple assignment that repeats facts already implied by the current symbolic state.
- An assertion before return that copies `Ensure` without a separate mathematical exit step.
- An assertion with no stable semantics that merely suppresses a temporarily unprovable VC.

A named semantic cut point may be retained when several paths join and complex branching or calls remain downstream. For a call or resource-connection assertion with no suitable domain predicate, `named_semantic_state` may be `none`, but its connection role must still be explained. If removing the assertion merely moves the mathematical obligation to invariant preservation, a call boundary, or a return witness, the fact that a VC still exists is not a reason to retain it.

## QCP-evidence checks

The exact `controller.py symexec` command must pass against the current main root and current round. The controller code fixes the driver, working directory, and canonical include/SLP options; the agent does not copy these fields into the report.

Inspect the controller's final status, not only the underlying main-root return code or a digest computed by the agent. Owner symbolic execution only refreshes the main-root generated files transactionally; the later main-owned acceptance check performs the independent clean replay. Two identical consecutive main-root digests do not replace that freshness gate. Never hand-edit the manual or weaken a correct specification/invariant merely to reduce split goals. If an expected-unchanged annotation repeatedly fails, pass the compact first failure to the main agent for a controller-owned retry or tooling repair decision.

Return `failed` if evidence points to a stale file, stale line, or stale directory. If a qcp-mcp interactive check came from a shared stateful session, return `failed` or `skipped` and state why.

## Teaching comparisons

- The positive example `QCP_examples/LLM_bench/Algorithms/majority_element/majority_element.c` uses `IsMajorityElement` and `MajorityOnReduced` to state the mathematical relationship among the candidate, vote count, and reduced state directly rather than reproducing Boyer-Moore control flow.
- For a positive binary-answer example, see `../annotation-filling/docs/correct-examples/binary-search-annotation.md` and its `split_array_largest_sum/` materials: `check` exposes a feasibility decision, and the main loop invariant keeps the true answer within the current bounds.
- For a negative example, see `../annotation-filling/docs/incorrect-examples/algorithm-mirror.md` and its `max_sub_array` files: defining a Kadane-style Rocq loop first and then making the annotations follow that loop is a specification-direction error.

These examples illustrate annotation/specification design only. Do not copy another case's proof scripts, generated artifacts, or formal-file structure.

## Decision

- Missing or misdirected specification: `failed`; return to `annotation-filling`.
- Algorithm-mirror specification, or a finite unique result hidden in a higher-order existential function without justification: `failed`; return to `annotation-filling` and redesign the representation.
- Reasonable specification not used by the C annotations: `failed`; repair the function specification or loop invariant.
- Ordinary `Assert` with no connection role, redundant with an invariant/postcondition, or present only to suppress a VC: `failed`; remove or revise it in the same annotation turn and rerun the check.
- Reasonable annotations and `formal_case_lib`, possibly needing a helper: `passed`, with a short risk summary.
- Stale input: recommend `stale` for the annotation result.
- Untrustworthy tool evidence, unclear file boundaries, or a bad specification/annotation direction: return `failed` and put a concise rework plan in the current `agent_output.md`, so annotation-filling can repair it in the same agent turn.
- A required annotation-checking tool is completely unusable and command evidence exists: recommend `blocked` for the annotation result.
- Context compaction: record only the `compact-error` fact; the controller/main agent decides whether to retry or ultimately block.

`passed` only means the candidate can be handed to the main agent for `annotation-check-round`. The main agent must still inspect the diff, evidence, and `formal_case_lib` contract, run canonical symbolic execution in the main root, and replay the same symbolic execution in an independent clean root to compare all four raw generated files plus manual declaration order/names/statements. This early gate also does not replace final-check.

## Rework-plan notes

On `failed`, write an immediately actionable rework plan in this attempt's `agent_output.md`. By default, the same annotation subagent continues repairing the candidate in the current turn. Each item should identify the failure class, repair target, message, and expected next check; add `self_reworkable` only when it genuinely helps scheduling. Put the predicate/specification review, any applicable higher-order-witness review, and the ordinary-`Assert` semantic review here as well; do not extend the terminal-report JSON. On a later iteration appended by the main agent, first reread both annotation skills in full, the main-agent blocker summary, and every original Markdown/JSON blocker file listed by the handoff.

`spec-quality`, `formal_case_lib-coqc`, `qcp-symbolic-execution`, `where-instantiation`, `invariant-too-weak`, `invariant-too-strong`, and `resource-loss` are repairable in the current spawn by default. Do not recommend terminal `blocked` for these failures. Notes may briefly record the number of repair attempts, but must not promote a repairable problem to a hard blocker.

The terminal report contains only the three check statuses. Failure evidence, qcp-mcp interaction hints, and the rework plan belong in `agent_output.md`.
