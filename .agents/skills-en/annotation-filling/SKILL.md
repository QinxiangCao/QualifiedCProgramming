---
name: annotation-filling
description: Use when the controller first delivers an annotation attempt for a run, or appends annotation gaps summarized from annotation-check or parent/group results to the same owner; the run's sole, persistently reused annotation agent adds or repairs the target C annotation in main root, maintains the mathematical specification in an existing formal_case_lib, and invokes annotation-checking within the same work session.
---

# Annotation Filling

You are the sole annotation owner for this run. Reuse the current agent target for the first attempt and every retry; do not create a replacement owner, read the root `AGENTS.md`, the orchestrator, or another role's skill, or infer, start, or repair a later proving phase.

## Required reading

1. Read the [filling and repair workflow](workflows/annotation-filling.md) in full.
2. Within the same work session, read [annotation-checking](../annotation-checking/SKILL.md) and its [workflow](../annotation-checking/workflows/annotation-checking.md) in full, and complete the checking loop as they require.
3. Read the [Annotation guide](docs/annotation-guide.md), [predicate-first design](docs/predicate-first-annotation.md), [placement of ordinary Assert statements](docs/semantic-assert-placement.md), and [QCP reference](docs/qcp-reference-guide.md).
4. When the task involves the corresponding structure, also read [arrays and strings](docs/array-string-guide.md), [branch control](docs/branch-control-annotation.md), or [pure proposition predicates](docs/pure-proposition-predicates.md).
5. If the controller handoff for this attempt explicitly names a correct or incorrect example within this skill, read the named file; do not expand the reading scope to another role's documents on your own.

The workflow is authoritative for the detailed input interpretation, write boundary, command contract, aggregated-feedback handling, checking loop, reporting, and finalize-repair rules.
