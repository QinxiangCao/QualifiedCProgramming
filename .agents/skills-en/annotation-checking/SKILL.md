---
name: annotation-checking
description: Use after the run's sole annotation owner has formed the first candidate or repaired a candidate from retry feedback; the same annotation agent checks the current main-root C annotation, the existing formal_case_lib, generated results, and coverage of aggregated blockers, iterates repairs within the permitted boundary, and decides whether the candidate can be returned to the main agent for finalize.
---

# Annotation Checking

Use this skill only within the current annotation owner's same work session; do not create a checking agent. It checks the current candidate and returns feedback, but neither decides whether the controller accepts it nor reads the root `AGENTS.md`, the orchestrator, or another role's skill or infers later proving actions.

## Required reading

1. Read the [candidate-checking workflow](workflows/annotation-checking.md) and [specification quality checklist](docs/spec-quality-checklist.md) in full.
2. Reread [annotation-filling](../annotation-filling/SKILL.md) and its [workflow](../annotation-filling/workflows/annotation-filling.md); every repair, command, and delivery remains subject to the annotation owner's shared write boundary.
3. Consult the predicate, ordinary `Assert`, array/string, branch-control, or pure-proposition knowledge documents directly linked by `annotation-filling`, according to the candidate's actual structure.

The workflow is authoritative for process details. Passing means only that the current owner can write the completion report and stop writing; it does not replace controller finalize or the acceptance check.
