---
name: annotation-filling
description: Used by the run's one persistent annotation subagent to add or repair C annotations in the main root and maintain the formal_case_lib specification declarations under SeparationLogic; it invokes annotation-checking before returning.
---

# Annotation Filling

A run may have only one annotation subagent. At initial startup, read `annotation-attempts/annotation-attempt1/agent_input.md`, this skill, the annotation-checking skill, all linked rules, and the correct/incorrect examples relevant to the current algorithm in full. After returning, keep the same agent target available for appended work; never ask the main agent to open another annotation agent.

Whenever a task is appended, first reread this skill and the annotation-checking skill in full. Then read the main agent's blocker conclusion, causal analysis, reflection on the previous attempt, required repair, and scope decision in the current `annotation-attempts/annotation-attemptN/agent_input.md`, together with every original blocker Markdown and JSON file listed there. Use the handoff summary to locate and prioritize the problem, and use the original evidence plus the current main-root files to verify facts. Do not rely only on either side or on memory from an earlier turn.

## Documentation

- `docs/annotation-guide.md`: specifications, invariants, external declarations, and the repair loop.
- `docs/qcp-reference-guide.md`: QCP syntax, reference policy, and scripted symbolic-execution evidence.
- `../verification-orchestrator/docs/path-configuration.md`: symbolic-execution and Coq path configuration.
- Other linked guides cover arrays/strings, branch control, pure predicates, and correct/incorrect examples.

## Allowed writes

- Annotations in the target `.c` file in the main root.
- Annotation-approved mathematical specification declarations in the main-root `formal_case_lib`.
- Generated files refreshed by `controller.py symexec` in the handoff's `Commands` section.
- The declared `agent_report.json` and `agent_output.md`.

Do not edit any other formal file, manual proof body, or group/proving file. Never edit generated files by hand.

## Production order

1. Read `problem_context` and the target C file.
2. Infer the mathematical business semantics and design or complete the `formal_case_lib` specifications.
3. Write C function specifications, loop invariants, assertions, and call instantiations.
4. Run the symbolic-execution command from the handoff's `Commands` section exactly as rendered. It must go through the controller; do not invoke an internal helper directly or assemble the driver, cwd, include, `-slp`, or output paths.
5. Run the `formal_case_lib` Coq command from the same block exactly as rendered. It must go through the controller; do not invoke an internal helper directly or assemble Coq flags or the build path.
6. Immediately before annotation-checking, run the handoff's `timing-stage ... start` command exactly as rendered. Invoke annotation-checking and complete its feedback-driven repair/recheck loop in the same agent turn. After the entire check is complete, run the matching `timing-stage ... finish` command exactly as rendered. Never substitute estimated timings for these boundaries.

A missing existing `formal_case_lib`, empty problem context, one tool failure, incomplete `where`, or an imperfect initial specification is not a terminal blocker. The controller provides a seed/path, and the owner must bootstrap or repair it in the current turn. On the third or a later annotation iteration, reevaluate the overall relationship among the mathematical specification, function contracts, loop invariants, assertions, and call instantiations instead of stacking another local patch.

## Forbidden compromises

- Do not weaken a postcondition or invariant merely to reduce the number of VCs.
- Do not disguise a mirror of the C algorithm as a mathematical definition and call it a functional specification.
- Do not add `Admitted.`, an extra `Axiom`, an unsound shortcut, or an import of a generated artifact.
- Do not invoke raw symexec, raw Coq, Dune, or Rocq MCP.
- qcp-mcp is only for C annotation/symbolic-execution interaction, not Rocq proof work.

## Result

The current `annotation-attempts/annotation-attemptN/agent_report.json` uses the flat `qcp-agent-report/v3` format. It records only this iteration's terminal status, exact changed files, the three `symexec` / `formal_case_lib` / `annotation_checking` check statuses, and concrete blockers. Put failure history, branch-control explanations, and a repair summary in the sibling `agent_output.md`; do not copy complete command evidence, rules, or iteration logs into JSON. After return, the controller seals the report/output digests. Later attempts do not overwrite these three files, and the controller stores formal before/after history separately.

Use `blocked` only when a required scripted tool is completely unusable, or when sufficient local attempts establish that the task cannot be completed from the current input. Use `stale` for an invalidated version. For compaction, record only the `compact-error` fact. The owner never writes `accepted`.
