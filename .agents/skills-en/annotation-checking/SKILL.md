---
name: annotation-checking
description: Used by the annotation subagent to inspect the current C annotations and formal_case_lib specifications in the main root and decide whether the candidate is ready for the main agent's annotation-check-round.
---

# Annotation Checking

Before entering this skill, the annotation owner must run the current handoff's `timing-stage ... start` command so that the complete review, feedback repair, and recheck are included in one interval. Run the matching `timing-stage ... finish` command only after this skill reaches a stable conclusion. This skill does not estimate elapsed time or write timing data to the agent report.

Use this skill inside the current turn of the run's one and only annotation agent. Do not start another agent. Whenever the main agent appends a new blocker-summary handoff, the annotation owner must first reread this skill and the annotation-filling skill in full, then read the main-agent summary and every original Markdown/JSON evidence file it names before making repairs or performing checks.

## Documentation

- `docs/spec-quality-checklist.md`: preflight checks for `formal_case_lib`, function specifications, invariants, scripted QCP/Coq evidence, and generated VCs.
- `../verification-orchestrator/docs/path-configuration.md`: path-assembly rules.

## Required checks

- `formal_case_lib` defines the mathematical meaning of the problem, and every external predicate referenced by the C annotations is declared.
- `formal_case_lib` contains no `Admitted.`, extra `Axiom`, or import of a current generated artifact.
- The exact handoff command `controller.py coq-check --target-kind formal-case-lib` passed.
- Function specifications describe the computed result, not only bounds and shape.
- Loop invariants cover initialization, preservation, and exit, connecting processed state to the postcondition.
- The exact handoff command `controller.py symexec` passed; canonical include/SLP options are fixed by controller code.
- Generated files were refreshed only by scripted symbolic execution.
- Changed files stay within the paths allowed by the handoff.

## Output

Write the final decision to `checks.annotation_checking` in the annotation report. If rework is required, briefly describe the findings, repair target, and residual risk in `agent_output.md`; do not nest evidence or a rework template in JSON.

`passed` means only that the candidate is ready for the controller's main-owned check; it does not mean accepted. For repairable specification, QCP, or `formal_case_lib` problems, return `failed + rework_plan` so annotation-filling can repair them in the same agent turn. Recommend `blocked` only when a required tool is completely unusable. Recommend `stale` when the version is obsolete. For compaction, record only the `compact-error` fact; never request a second annotation agent.
