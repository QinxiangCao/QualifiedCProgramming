# Specification Quality Checklist

The purpose of this check is not to prove every VC. It is to catch clearly incorrect C annotations and `formal_case_lib` content before `annotation-check-round`.

## `formal_case_lib`

For every external Rocq predicate, function, or relation used in the C annotations, confirm that:

- Its declaration exists and its name, arity, and parameter order match the C annotations.
- The handoff command `controller.py coq-check --target-kind formal-case-lib` passes. The agent must not invoke the internal helper directly or assemble the target/build path itself.
- Its contents are a mathematical specification, not a reproduction of the current C program's control flow.
- It is strong enough to derive the result semantics in the function's `Ensure`, without making one implementation strategy the only permitted behavior.
- It contains no `Admitted.`, extra `Axiom`, or `SimpleC.EE.*` import of a generated artifact for the current case.

If a definition is missing, points in the wrong direction, or its evidence refers to the wrong path, return `failed` and require a repair in `annotation-filling`.

## Function-specification checks

A function specification must distinguish at least three categories of facts:

- Execution facts: integer ranges, index ranges, loop bounds, and overflow limits.
- Memory facts: arrays, lists, structures, pointers, and owned resources.
- Logical properties: what the function computes mathematically.

The third category must answer “what does the result mean?” For example, sorting requires sortedness and permutation, searching requires found/not-found semantics, and optimization requires feasibility, optimality, or an extremum definition. A specification containing only shape, bounds, and a return-value range is usually insufficient.

## Loop-invariant checks

A loop invariant must include at least:

- Variable ranges, index relationships, and integer-overflow limits.
- The currently owned array, list, buffer, or other memory resources.
- The mathematical relationship between the processed portion and the overall goal.

Common failures include having only bounds and array resources, referring directly to a Rocq version of the loop function, being unable to derive the `Ensure` at exit, failing initialization or preservation, or omitting `@pre` bridges, local-variable bindings, or live local resources from a full assertion.

## QCP-evidence checks

The exact `controller.py symexec` command must pass against the current main root and current round. The controller code fixes the driver, working directory, and canonical include/SLP options; the agent does not copy these fields into the report.

Return `failed` if evidence points to a stale file, stale line, or stale directory. If a qcp-mcp interactive check came from a shared stateful session, return `failed` or `skipped` and state why.

## Semantic preflight of generated VCs

After canonical QCP generates the current case's proof artifacts, you may read the generated context allowed for the current round and check whether witness shapes expose a direction error in the annotations or specification. Do not use generated/proof artifacts from another case as evidence.

Warning signs include:

- After a destructive array write, the postcondition still requires the entire mutable logical list to remain a `Permutation` / `sorted_permutation` of the old input.
- The invariant does not distinguish the immutable source, mutable destination, processed prefix, and unconstrained suffix.
- After the loop body overwrites or moves elements, an assertion continues to use an old full-list equality or old full-list multiset.
- The postcondition requires an unchanged suffix or multiplicity even though the C code may overwrite the suffix.

This step does not prove every manual VC. It only decides whether the obligations are already semantically and obviously unprovable.

## Decision

- Missing or misdirected specification: `failed`; return to `annotation-filling`.
- Reasonable specification not used by the C annotations: `failed`; repair the function specification or loop invariant.
- Reasonable annotations and `formal_case_lib`, possibly needing a helper: `passed`, with a short risk summary.
- Stale input: recommend `stale` for the annotation result.
- Untrustworthy tool evidence, unclear file boundaries, or a bad specification/annotation direction: return `failed` and put a concise rework plan in the current `agent_output.md`, so annotation-filling can repair it in the same agent turn.
- A required annotation-checking tool is completely unusable and command evidence exists: recommend `blocked` for the annotation result.
- Context compaction: record only the `compact-error` fact; the controller/main agent decides whether to retry or ultimately block.

`passed` only means the candidate can be handed to the main agent for `annotation-check-round`. The main agent must still inspect the diff, evidence, and `formal_case_lib` contract and run canonical symbolic execution in the main root.

## Rework-plan notes

On `failed`, write an immediately actionable rework plan in this attempt's `agent_output.md`. By default, the same annotation subagent continues repairing the candidate in the current turn. Each item should identify the failure class, repair target, message, and expected next check; add `self_reworkable` only when it genuinely helps scheduling. On a later iteration appended by the main agent, first reread both annotation skills in full, the main-agent blocker summary, and every original Markdown/JSON blocker file listed by the handoff.

`spec-quality`, `formal_case_lib-coqc`, `qcp-symbolic-execution`, `where-instantiation`, `invariant-too-weak`, `invariant-too-strong`, and `resource-loss` are repairable in the current spawn by default. Do not recommend terminal `blocked` for these failures. Notes may briefly record the number of repair attempts, but must not promote a repairable problem to a hard blocker.

The terminal report contains only the three check statuses. Failure evidence, qcp-mcp interaction hints, and the rework plan belong in `agent_output.md`.
