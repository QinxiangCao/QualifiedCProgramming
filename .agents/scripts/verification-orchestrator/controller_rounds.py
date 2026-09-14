#!/usr/bin/env python3
"""Round creation, compact Markdown handoffs, stepping, and group scheduling."""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path
from typing import Any

from controller_dune import _preparation_action
from controller_invocations import (
    hydrate_actions,
    hydrate_waiting_deliveries,
)
from controller_state import (
    GENERATED_KEYS,
    _append_event,
    _archive_annotation_stage,
    _current_files_errors,
    _file_digest,
    _formal_case_lib_is_active,
    _json_load,
    _load_state,
    _manual_obligations,
    _proof_manual_sha256,
    _run_root_from_id,
    _save_state,
    _utc,
    _validated_annotation_attempt_paths,
    _validated_proving_attempt_paths,
)
from coq_tooling import dune_preparation_receipt_errors
from path_utils import (
    annotation_attempt_directory_name,
    annotation_attempt_report_root,
    annotation_history_root,
    fixed_path_under,
    round_report_root,
    write_json,
    write_text,
)
from prepare_group_workers import resolve_group_workers_manifest
from symexec_tooling import _lexical_regular_file_snapshot

DEFAULT_MAX_PARALLEL_GROUP_WORKERS = 5
VC_PROVING_PHASE = "vc-proving-preparing"
ANNOTATION_GAP_FAILURE_CLASS = "annotation-gap"
# A delivery carries formal sources and owner narrative. Feedback cites the
# narrative; report-only repair preserves the formal bytes.
FORMAL_ARTIFACT_ROLES = ("proof_manual", "group_worker_lib")
NOTES_ARTIFACT_ROLE = "output"
GROUP_NOTES_FILENAME = "group_worker_output.md"
GROUP_VC_CHECKING_FAILURE_CLASSES = frozenset(
    {"plan-defect"}
)
VC_CHECKING_BLOCKER_RETRY_PHASES = {
    ANNOTATION_GAP_FAILURE_CLASS: "annotation",
    "specification-gap": "annotation",
    "dependency-gap": "annotation",
    "plan-defect": "vc-checking",
    "report-defect": "vc-checking",
    "infrastructure": "vc-checking",
}


def _annotation_plan_template() -> dict[str, Any]:
    return {
        "version": 2,
        "status": "planning",
        "function_specs": [],
        "loop_invariants": [],
        "new_predicates": [],
        "vc_comparisons": [],
    }


def _round_paths(report_root: Path, round_id: str) -> dict[str, Path]:
    directory = fixed_path_under(
        report_root / "rounds" / round_id,
        report_root,
        label="phase round report directory",
    )
    directory.mkdir(parents=True, exist_ok=True)
    return {
        "directory": directory,
        "input": directory / "agent_input.md",
        "report": directory / "agent_report.json",
        "output": directory / "agent_output.md",
        "group_plan": directory / "group_plan.json",
    }


def _annotation_paths(run_root: Path, annotation_iteration: int) -> dict[str, Path]:
    directory = annotation_attempt_report_root(run_root, annotation_iteration)
    return {
        "directory": directory,
        "input": directory / "agent_input.md",
        "report": directory / "agent_report.json",
        "output": directory / "agent_output.md",
        "plan": directory / "annotation_plan.json",
        "group_plan": directory / "group_plan.json",
    }


def _spawn_message(input_path: Path, report_path: Path) -> str:
    return (
        f"Read {input_path} completely and follow it as the source of truth. "
        f"Complete the assigned phase in one spawn when possible, then write the terminal result to {report_path}. "
        "Controller acceptance is separate."
    )


def _annotation_spawn_message(action: dict[str, Any]) -> str:
    return (
        f"Spawn the run's only annotation agent and retain its target as session {action['session_id']}. "
        f"Tell it to read {action['input']} completely, including annotation-designing and the relevant "
        f"examples selected there, then write the terminal result to {action['report']}. "
        "Do not close or replace this agent after it returns; controller acceptance is separate."
    )


def _annotation_append_message(action: dict[str, Any]) -> str:
    feedback = ", ".join(
        str(path)
        for item in action.get("feedback_sources", [])
        for path in item.get("evidence", [])
    )
    return (
        f"Append this task to the existing annotation agent session {action['session_id']}; do not spawn a new agent. "
        f"Before editing, reload .agents/skills/annotation-designing/SKILL.md completely, then read the controller handoff and "
        f"repair handoff {action['input']} plus its original blocker evidence ({feedback}). "
        "Revise the current main-root formal C annotation and edit the case lib "
        "only when the handoff marks that existing path writable, "
        f"use the controller checks as needed for feedback, compare every failed VC after symexec, "
        f"and write the terminal result to {action['report']}."
    )


def _rules_source(phase: str) -> list[str]:
    result = [
        ".agents/skills/verification-orchestrator/SKILL.md",
        ".agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md",
        ".agents/skills/verification-orchestrator/workflows/paths-and-commands.md",
    ]
    if phase == "annotation":
        result.extend(
            [
                ".agents/skills/annotation-designing/SKILL.md",
                ".agents/skills/annotation-designing/workflows/annotation-designing.md",
            ]
        )
    else:
        result.extend(
            [
                ".agents/skills/vc-checking/SKILL.md",
                ".agents/skills/vc-checking/workflows/vc-analysis-and-grouping.md",
            ]
        )
    return result


def _controller_command(state: dict[str, Any], command: str, *args: str) -> str:
    controller = (
        Path(str(state["main_root"]))
        / ".agents"
        / "scripts"
        / "verification-orchestrator"
        / "controller.py"
    )
    argv = [
        sys.executable,
        str(controller),
        "--main-root",
        str(state["main_root"]),
        command,
        "--run",
        str(state["run_id"]),
        *args,
    ]
    return subprocess.list2cmdline(argv) if os.name == "nt" else shlex.join(argv)


def _controller_command_execution_contract() -> str:
    return """## Controller command execution contract

Run every listed controller command unchanged with its bound cwd. Prefer a direct system-terminal call. If the runtime
exposes terminal tools only through `functions.exec`, use a transparent bridge. Each bridge cell may await exactly one
terminal operation: `tools.exec_command` to launch the command, or `tools.write_stdin` to continue the same live
session (or the runtime-documented normalized name for that same terminal operation), and may only forward its result.
Pass the rendered command/argv, every argument, and cwd unchanged when launching, and preserve the exact session
handle when continuing. A normalized equivalent is permitted only when its input shape accepts those values unchanged;
never serialize an argv array into shell text, reparse a rendered command, or add quoting.

Do not call a second tool in a bridge cell, add JavaScript/Python orchestration, construct, alter, sequence,
parallelize, or interpret commands, wrap them in a generated shell/PowerShell/Python script or another `uv run`, use
`sh -c`, command substitution, a pipeline or background execution, or invoke another wrapper. Never recreate
controller behavior with a custom command or script.

Preserve every outer cell and inner process/session handle until the actual command reaches a terminal exit. If a
transparent bridge yields a running `functions.exec` cell, resume only that cell with `functions.wait` until its one
nested terminal operation returns. Empty output, an initial-yield response, and outer-cell messages such as
`Script completed` do not prove that the controller command finished. Record a check as passed only after the terminal
process exits with code 0 and the controller JSON reports
`status: passed`."""


def _agent_report_payload() -> dict[str, Any]:
    """Create the only owner-authored machine declaration.

    Diff, version and check evidence are controller facts.  Keeping those
    fields in an owner report merely asks an agent to copy data which the
    controller must recompute before acceptance anyway.
    """

    return {
        "status": "pending",
    }


def _vc_decision_summary_skeleton() -> str:
    return """# VC Decision Summary

## Outcome

- Status: pending
- Witnesses: 0
- Groups: 0
- Expected critical path: pending

## Structural Blocker Scan

- Status: pending
- Top-level VCs scanned: 0
- No-split VCs checked first: 0
- Definite blockers: 0

## Annotation Comparison Review

| Source VC | Current / Related VCs | Premise sources | Independent assessment | Risk |
|---|---|---|---|---|

## Proof-Mode Decisions

| VC | Mode | Reason |
|---|---|---|

## Common Proof Patterns

### P1: <pattern name>

- Applies to: <VCs>
- Common idea: <write once>
- Planned helper owner: <group or none>

## VC Deltas

| VC | Pattern | Only the difference |
|---|---|---|

## Grouping Decisions

| Group | Why together | Why not merged further |
|---|---|---|

## Risks or Blockers

- none
"""


def _format_list(items: list[str], *, empty: str = "none") -> str:
    return "\n".join(f"- `{item}`" for item in items) if items else f"- {empty}"


def _previous_vc_proving_round(state: dict[str, Any]) -> str | None:
    """Return the immediately preceding proving round recorded by the controller."""

    for attempt_id in reversed(state["attempts"]):
        attempt = state["attempts"][attempt_id]
        if (
            isinstance(attempt, dict)
            and attempt.get("phase") == VC_PROVING_PHASE
            and isinstance(attempt.get("round"), str)
        ):
            return str(attempt["round"])
    return None


def _stable_fixed_file_snapshot(
    path: Path,
    *,
    owner: Path,
    label: str,
) -> dict[str, Any]:
    """Read one exact controller-owned file without following replacements."""

    try:
        fixed_owner = fixed_path_under(owner, owner.parent, label=f"{label} owner")
        fixed_path = fixed_path_under(path, fixed_owner, label=label)
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    try:
        relative = fixed_path.relative_to(fixed_owner).as_posix()
    except ValueError as exc:
        raise ValueError(f"{label} escaped its fixed owner") from exc
    snapshot = _lexical_regular_file_snapshot(
        root=fixed_owner,
        relative=relative,
        label=label,
    )
    if snapshot.get("state") != "present":
        detail = str(snapshot.get("message") or "artifact is missing")
        raise ValueError(
            f"{label} is not a readable non-link regular file: {detail}"
        )
    return snapshot


def _problem_context_text(context: dict[str, Any]) -> str:
    lines: list[str] = []
    for key, value in context.items():
        if key == "source" or value in ("", [], None):
            continue
        label = key.replace("_", " ").title()
        if isinstance(value, list):
            lines.append(f"- {label}: " + "; ".join(str(item) for item in value))
        else:
            lines.append(f"- {label}: {value}")
    return (
        "\n".join(lines)
        if lines
        else "- Infer a conservative mathematical specification from the target C file."
    )


def _target_file_is_present(state: dict[str, Any], key: str) -> bool:
    return (
        Path(str(state["main_root"])) / str(state["target_files"][key])
    ).is_file()


def _optional_annotation_artifact_lines(
    state: dict[str, Any], *, annotation_owner: bool = True
) -> str:
    target = state["target_files"]
    formal_case_lib_active = _formal_case_lib_is_active(state)
    policy = str(state["formal_case_lib_policy"])
    formal_case_lib_status = (
        (
            f"present under `{policy}` policy; edit it only during an allowed design/proof-helper step"
            if annotation_owner
            else f"present under `{policy}` policy; read-only in this phase"
        )
        if formal_case_lib_active
        else (
            "missing under explicit `absent` policy; there is no active/editable "
            "case lib, and this candidate path is read-only and must not be created"
        )
    )
    manual_status = (
        "present; generated/proved artifact, never edit it as annotation source"
        if _target_file_is_present(state, "proof_manual_file")
        else (
            "missing; this is an optional generated artifact, and only controller "
            "symbolic execution may create it"
        )
    )
    return (
        f'- `formal_case_lib` candidate ({formal_case_lib_status}): '
        f'`{target["formal_case_lib"]}`\n'
        f'- Manual ({manual_status}): `{target["proof_manual_file"]}`'
    )


def _annotation_commands(state: dict[str, Any], round_id: str) -> tuple[str, bool]:
    formal_case_lib_present = _formal_case_lib_is_active(state)
    design_check = _controller_command(
        state,
        "coq-check",
        "--round",
        round_id,
        "--target-kind",
        "formal-case-lib-design",
    )
    commands = [
        design_check,
        _controller_command(state, "symexec", "--round", round_id),
    ]
    if formal_case_lib_present:
        commands.append(
            _controller_command(
                state,
                "coq-check",
                "--round",
                round_id,
                "--target-kind",
                "formal-case-lib",
            )
        )
    return "\n".join(commands), formal_case_lib_present


def _formal_case_lib_command_explanation(present: bool) -> str:
    if present:
        return (
            "The standalone design check may be rerun after each specification or "
            "case-lib change and does "
            "not require generated goals. The later formal-case-lib Coq command uses the controller's single "
            "skinny-build plan: it stages only the exact current-case dependency "
            "closure, loads or builds its current prerequisites from the "
            "content-addressed cache, and reads fixed dependency `.vo` files from "
            "the selected sealed base. Before this local check, the controller asks "
            "the selected backend to prepare the exact case-lib target. A dependency "
            "that is merely unbuilt is therefore not an annotation defect."
        )
    return (
        "This run explicitly selected the absent policy. The standalone design "
        "check records a skipped pass; no post-symexec "
        "formal-case-lib command is listed, and the owner must keep the candidate path absent."
    )


def _narrative_paths(paths: dict[str, Path]) -> dict[str, Path]:
    """Drop the formal sources of a delivery, keeping the owner narrative."""

    return {
        role: path
        for role, path in paths.items()
        if role not in FORMAL_ARTIFACT_ROLES
    }


def _feedback_source_line(item: dict[str, Any]) -> str:
    """Render one feedback source as its sealed evidence paths."""

    paths = "; ".join(f"`{path}`" for path in item["evidence"])
    return f"- `{item['phase']}` / `{item['attempt_id']}`: {paths}"


def _current_annotation_comparisons(state: dict[str, Any]) -> list[dict[str, Any]]:
    accepted = state["accepted_rounds"]["annotation"]
    attempt = state["attempts"][accepted["attempt_id"]]
    plan = _json_load(_validated_annotation_attempt_paths(state, attempt)["plan"], {})
    return [dict(item) for item in plan["vc_comparisons"]]


def _render_annotation_retry_handoff(
    state: dict[str, Any],
    *,
    round_id: str,
    attempt_id: str,
    paths: dict[str, Path],
    allowed_write_paths: list[str],
    previous_attempts: list[dict[str, Any]],
    required_lessons: list[dict[str, Any]],
    annotation_iteration: int,
    feedback_sources: list[dict[str, str]],
    retry_reason: str,
    failed_vcs: list[dict[str, Any]],
    previous_vc_changes: list[dict[str, Any]],
) -> str:
    target = state["target_files"]
    session = state.get("annotation_session")
    session_id = (
        str(session["session_id"])
        if isinstance(session, dict)
        else f"{state['case']}-annotation-agent"
    )
    source_lines = (
        "\n".join(
            _feedback_source_line(item)
            for item in feedback_sources
        )
        or "- No external phase files; inspect the controller-recorded failure below."
    )
    prior_lines = (
        "\n".join(
            f"- `{item['attempt_id']}`: report `{item['report']}`; notes `{item['output']}`"
            for item in previous_attempts
        )
        or "- none"
    )
    blocker_details = (
        "\n".join(f"- {item.get('must_address', item)}" for item in required_lessons)
        or "- No additional controller evidence."
    )
    failed_vc_text = "\n".join(
        (
            f"{index}. `{item['source_attempt']}:{item['name']}`\n"
            f"   - Parent: `{item['parent'] or 'none'}`\n"
            f"   - Annotation location: {item['annotation_location']}\n"
            f"   - Sealed manual: `{item['manual']}`\n"
            f"   - Old gap: {item['message']}"
        )
        for index, item in enumerate(failed_vcs, start=1)
    ) or "- none"
    history_text = "\n".join(
        (
            f"{index}. `{item['source']['attempt']}:{item['source']['name']}`\n"
            f"   - Old gap: {item['old_gap']}\n"
            f"   - Change: {item['change']}\n"
            f"   - Current VC: {', '.join(item['current'])}\n"
            f"   - Result: `{item['result']}`"
        )
        for index, item in enumerate(previous_vc_changes, start=1)
    ) or "- none"
    rules = _format_list(_rules_source("annotation"))
    commands, formal_case_lib_present = _annotation_commands(state, round_id)
    formal_case_lib_command_explanation = _formal_case_lib_command_explanation(
        formal_case_lib_present
    )
    return f"""# Annotation retry handoff

This is annotation iteration {annotation_iteration} in the run's single persistent annotation-agent session. Read the sealed failed VCs, edit the current annotation, run symbolic execution, and compare every old VC with the current manual.

## Assignment

- Session: `{session_id}`
- Round: `{round_id}`
- Attempt: `{attempt_id}`
- Retry reason: `{retry_reason}`
- Main root: `{state["main_root"]}`
- Terminal report: `{paths["report"]}`
- Human notes: `{paths["output"]}`
- Annotation plan: `{paths["plan"]}`

## Target files

- C: `{target["c_file"]}`
{_optional_annotation_artifact_lines(state)}
- Goal/auto/check: `{target["goal_file"]}`, `{target["proof_auto_file"]}`, `{target["goal_check_file"]}`

## Original blocker evidence

{source_lines}

Previous annotation attempt artifacts:

{prior_lines}

Controller-recorded blocker details:

{blocker_details}

## Failed VCs

{failed_vc_text}

## Previous VC changes

{history_text}

## Rules to reload

The annotation agent must completely reload annotation-designing on every appended iteration, then follow all linked rules and inspect the original blocker evidence, sealed manuals, and current main-root files above.

{rules}

## Writable formal paths

{_format_list(allowed_write_paths)}

Generated files may change only through the exact symbolic-execution command below.
{_spec_freeze_section(state)}
{_controller_command_execution_contract()}

## Commands

```text
{commands}
```

{formal_case_lib_command_explanation}

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

## Completion

Function specs, necessary predicates, body `Assert` / `Inv Assert` annotations, case-lib definitions and lemmas, and `{paths["plan"]}` may change together when the spec is agent-written or after `unfreeze`. Reuse core predicates directly and do not add synonymous wrapper layers. Do not add any other kind of body annotation. After symexec, compare each failed proposition with the current manual and record only the old gap, the annotation change, and whether it is resolved. Keep editing while a result is `unresolved`. Submit only when every failed VC is `resolved`. Do not edit the proof manual or write proofs. Success contains only `status: completed`. Notes are optional.
"""


def _spec_freeze_section(state: dict[str, Any]) -> str:
    """Render the user-provided or agent-written specification workflow."""

    record = state.get("spec_freeze")
    if isinstance(record, dict) and record.get("functions"):
        functions = ", ".join(f"`{name}`" for name in record["functions"])
        if record.get("baseline") is None:
            return f"""
## User-provided specification after unfreeze

The user approved changes to {functions}. Apply the approved changes in this
attempt, then continue specification, internal annotation, case-lib, plan, and
symexec work together. Acceptance records the checked specification as the new
user-provided baseline.
"""
        return f"""
## User-provided specification

The specification of {functions} is a fixed input for this run, not something to
redesign. Their `With` / `Require` / `Ensure` blocks -- including named specs and any
`<= other_spec` clause -- must survive this attempt token-identical. Comments, whitespace
and line endings are free.

Because a frozen specification's meaning depends on the definitions behind it, every
`Extern Coq` entry, `Import Coq` module, and case-lib declaration that already exists is
frozen as well.

You may still add: new `Extern Coq` entries, new imports, new case-lib definitions and
lemmas, and specifications for functions not listed above. Every `Inv Assert` and `Assert`
stays fully editable -- those are the intended working surface.

If this specification itself must change, stop without modifying it or running
`finalize-delivery`. Write the exact function, reason, planned `With` / `Require` /
`Ensure` changes, meaning before and after, and effect on the requested result in
`agent_output.md`, then return that proposal to the main agent. Continue only after
the user agrees and the main agent runs `unfreeze` for this same round.
"""
    return """
## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.
"""


def _render_agent_input(
    state: dict[str, Any],
    *,
    phase: str,
    round_id: str,
    attempt_id: str,
    paths: dict[str, Path],
    allowed_write_paths: list[str],
    previous_attempts: list[dict[str, Any]],
    required_lessons: list[dict[str, Any]],
    attempt_index: int,
    annotation_iteration: int = 0,
    feedback_sources: list[dict[str, str]] | None = None,
    retry_reason: str | None = None,
    failed_vcs: list[dict[str, Any]] | None = None,
    previous_vc_changes: list[dict[str, Any]] | None = None,
) -> str:
    if phase == "annotation" and annotation_iteration > 1:
        return _render_annotation_retry_handoff(
            state,
            round_id=round_id,
            attempt_id=attempt_id,
            paths=paths,
            allowed_write_paths=allowed_write_paths,
            previous_attempts=previous_attempts,
            required_lessons=required_lessons,
            annotation_iteration=annotation_iteration,
            feedback_sources=feedback_sources or [],
            retry_reason=str(retry_reason or "annotation-feedback"),
            failed_vcs=failed_vcs or [],
            previous_vc_changes=previous_vc_changes or [],
        )
    target = state["target_files"]
    rules = _format_list(_rules_source(phase))
    previous = _format_list(
        [
            " | ".join(
                str(item.get(key))
                for key in (
                    "attempt_id",
                    "report",
                    "output",
                    "annotation_history_directory",
                )
                if item.get(key)
            )
            for item in previous_attempts
        ]
    )
    lessons = (
        "\n".join(f"- {item.get('must_address', item)}" for item in required_lessons)
        or "- none"
    )
    common = f"""# {phase} handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `{round_id}`
- Attempt: `{attempt_id}` (index {attempt_index})
- Main root: `{state["main_root"]}`
- Terminal report: `{paths["report"]}`
- Optional human notes: `{paths["output"]}`

## Target files

- C: `{target["c_file"]}`
{_optional_annotation_artifact_lines(state, annotation_owner=phase == "annotation")}
- Goal/auto/check: `{target["goal_file"]}`, `{target["proof_auto_file"]}`, `{target["goal_check_file"]}`

## Rules to read

{rules}

## Previous attempts

{previous}

Required lessons:

{lessons}

{_controller_command_execution_contract()}
"""
    if phase == "annotation":
        commands, formal_case_lib_present = _annotation_commands(state, round_id)
        formal_case_lib_command_explanation = _formal_case_lib_command_explanation(
            formal_case_lib_present
        )
        feedback = feedback_sources or []
        feedback_text = (
            "\n".join(
                _feedback_source_line(item)
                for item in feedback
            )
            if feedback
            else "- none (initial annotation iteration)"
        )
        iteration_rules = (
            "This is the initial iteration. Read annotation-designing completely, follow its linked guides, "
            "and inspect the correct/incorrect examples relevant to this case before editing."
            if annotation_iteration == 1
            else "This is a continuation of the same annotation-agent session. Before editing, reload annotation-designing "
            "completely and read every listed Markdown and JSON blocker source; do not rely on a summary."
        )
        current_session = state.get("annotation_session")
        annotation_session_id = (
            str(current_session["session_id"])
            if isinstance(current_session, dict)
            else f"{state['case']}-annotation-agent"
        )
        return (
            common
            + f"""

## Persistent annotation agent

- Session: `{annotation_session_id}`
- Iteration: {annotation_iteration}

{iteration_rules}

Feedback appended for this iteration:

{feedback_text}

Annotation plan: `{paths["plan"]}`

## Problem context

{_problem_context_text(state.get("problem_context", {}))}

## Writable formal paths

{_format_list(allowed_write_paths)}

Generated files may change only through the exact symbolic-execution command below.
{_spec_freeze_section(state)}
## Commands

```text
{commands}
```

{formal_case_lib_command_explanation}

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

## Completion

Start with natural-language `Signature`, `Preconditions`, and `Output`, then write the equivalent Rocq and C specifications. Search the current dependencies and reuse core predicates directly; do not add synonymous wrapper layers. Write and revise the function spec, necessary predicates, body `Assert` / `Inv Assert` annotations, case-lib definitions and lemmas, and the concise annotation plan together as allowed above. Do not add any other kind of body annotation. The first attempt keeps `vc_comparisons` empty.
Use the listed commands when useful for feedback; controller acceptance reruns every mandatory machine check. If annotation work exposes another annotation gap, continue fixing it in this attempt instead of returning a blocked report. Write a success report containing only `status: completed`. On the first `symexec`
`tool` failure, keep this claimed attempt and every formal byte unchanged and
rerun the exact same controller command once; do not write a terminal report yet.
Only a second identical tool failure may produce a blocked result. Such a result adds one
complete `blocker`. Do not copy changed paths, version, or check status into the report.
"""
        )

    obligations = _manual_obligations(state)
    witnesses = [str(item) for item in obligations["top_level"]]
    comparisons = _current_annotation_comparisons(state)
    comparison_lines: list[str] = []
    for item in comparisons:
        current_names = ", ".join(
            "`" + str(name) + "`" for name in item["current"]
        )
        comparison_lines.append(
            f"- `{item['source']['name']}` -> {current_names}; "
            f"result `{item['result']}`; change: {item['change']}"
        )
    comparison_text = "\n".join(comparison_lines) or "- none (first proving round)"
    witness_lines: list[str] = []
    for name in witnesses:
        split_names = [str(item) for item in obligations["split_goals"].get(name, [])]
        split_text = (
            ", ".join(f"`{split_name}`" for split_name in split_names)
            if split_names
            else "none"
        )
        witness_lines.append(
            f"- `{name}`; generated split goals: {split_text}"
        )
    witness_text = "\n".join(witness_lines) if witness_lines else "- none"
    manual_debug_command = _controller_command(
        state, "coq-debug", "--round", round_id
    )
    helper_topology_rule = (
        "The fixed run topology contains `formal_case_lib`, so groups may plan "
        "owner-suffixed helpers when needed."
        if _formal_case_lib_is_active(state)
        else "The fixed run topology has no `formal_case_lib`: every group must "
        "omit `helpers`; do not plan a helper or assume a `group_worker_lib` exists."
    )
    return (
        common
        + f"""

## VC checking inputs

- Group plan output: `{paths["group_plan"]}`
- Maximum witnesses per group: {state["max_witnesses_per_group"]}

{helper_topology_rule}

Target witnesses:

{witness_text}

## Annotation VC comparisons

{comparison_text}

Independently check every claimed fact source against the current manual. A comparison marked `provable` is a priority check, not a proof result. Put its current and related VCs in the first, high-risk group when they require a new substantial mathematical lemma. Return an annotation blocker immediately when a current premise has no establishing VC or matching case-lib lemma.

Before exhaustive split analysis, perform one cheap structural scan over every top-level VC, checking no-split goals
first and looking specifically for missing resource addresses, scalar equalities, and current-to-@pre bridges. Record
the exact counts and outcome in the `Structural Blocker Scan` section of `{paths["output"]}`. A definite whole-goal
countermodel may be returned immediately as an annotation/specification/dependency blocker; do not spend time on all
split goals first. If this scan has no definite blocker, then judge every generated split goal across all target VCs,
without analyzing any top-level VC. In this pass, record only whether each split goal is provable; do not yet plan
helpers, proof strategies, or reuse. For a top-level VC with
at least one generated split goal, select `aggressive_pre_process` exactly when all of its split goals are provable; do
not analyze that top-level VC's provability. If any split goal is not provable, or no split goal exists, then judge only
the whole top-level VC's provability and select `LLM_pre_process` when it is provable. If that whole VC is not provable,
report the annotation/specification boundary instead of creating a proving assignment.

After every `proof_mode` is fixed, write the natural-language proof strategy. For
`aggressive_pre_process`, analyze only the split goals; do not write a top-level proof strategy. For
`LLM_pre_process`, analyze only the whole top-level VC. VC checking does not analyze proof reuse. On a retry, the
previous VC-checking reports listed above may be read for context, but the current main-root manual is authoritative.
Only after the strategies are complete, group the top-level VCs by their proof ideas. Never assign a split goal
independently: every split goal follows its parent top-level VC into the same group.

The C, goal, auto, check, and case library are read-only. You may temporarily edit the main-root manual
`{state['target_files']['proof_manual_file']}` to insert `Show.` while inspecting a goal; do not create a debug script.
Run this command unchanged after each useful edit:

```text
{manual_debug_command}
```

After this delivery is accepted, the controller deletes that manual and reruns symbolic execution so group workers
receive a clean generated manual.

Form initial groups by invariant, proof pattern, array/frame transformation, refinement
transition, and helper family. Then perform a second load-and-coupling review using top-level witness count, aggressive
split-goal count, expected helper families, proof-mode differences, program phase, and persistent proof context. Prefer
coherent groups of roughly 2--6 witnesses; justify every group above 6 witnesses and every single-witness group in
`{paths["output"]}`. Heavy aggressive/helper work should not be bundled with many lightweight projection/rewrite/lia
VCs. Explicitly review the expected critical path: for every likely tail group, record split/helper/library/context
load in `{paths["output"]}`, split final-result work from independently provable transition/safety work when helper
ownership permits, and otherwise explain the indivisible helper/context coupling. Plan stable permutation, sum/length,
mask-clear, and similar cross-group facts as annotation-approved or public helpers rather than rediscovering them in a
tail group. Assign each group an integer `estimated_difficulty` from 1 (light) to 5 (heaviest). Groups remain independent and
cannot read sibling outputs. Put every helper expected to be newly proved or modified in this round in the owner group's
plan with an exact Rocq declaration `name`, a short `strategy`, and `visibility` set to `local` or `public`. Mark a
stable mathematical helper useful to other groups as public. The controller promotes only successfully proved
matching public declarations into the run-level append-only candidate pool; workers copy candidates into their own
group_worker_lib and still pass the ordinary controller group validation. This pool is not an imported or active fourth library.

    Keep `{paths["output"]}` as a decision summary. Record proof-mode reasons, grouping and critical-path decisions,
    define each common proof pattern once, and give each VC only a pattern reference plus its actual delta. Do not copy
    this handoff, the JSON schema, controller commands, or identical proof steps into that Markdown. Write
    `group_plan.json`: each group has `id`, `estimated_difficulty`, witness objects with
`name` and `proof_mode`. An aggressive witness has `split_strategies`, mapping each generated split-goal name to its
short strategy in declaration order, and omits `strategy`. An `LLM_pre_process` witness has one whole-goal `strategy`
and omits `split_strategies`. Optional planned
helpers use `{{name, strategy, visibility}}`. Do not copy controller metadata or an acceptance marker into the plan.
Write the final report: success contains only `status: completed`; a
    blocked result adds one `blocker` with `failure_class`, `kind`, `vcs`, `message`, and `repair_boundary`. Each VC entry has exact `name`, `parent`, and `annotation_location`. Do not
copy controller checks into the report. Its `failure_class` must be exactly one of
`annotation-gap`, `specification-gap`, `dependency-gap`, `plan-defect`, `report-defect`, or
`infrastructure`. The controller routes the first three to annotation and the last three to a same-phase vc-checking
retry; it never infers the repair phase from `kind` or prose.
"""
    )


def _next_round_id(state: dict[str, Any], phase: str) -> str:
    prefix = f"{state['case']}-{phase}-r"
    used = [
        int(key.rsplit("r", 1)[-1])
        for key in state["rounds"]
        if key.startswith(prefix) and key.rsplit("r", 1)[-1].isdigit()
    ]
    return f"{prefix}{max(used, default=0) + 1}"


def _init_round_attempt(
    state: dict[str, Any],
    *,
    phase: str,
    previous_attempts: list[dict[str, Any]] | None = None,
    required_lessons: list[dict[str, Any]] | None = None,
    attempt_index: int = 1,
    feedback_sources: list[dict[str, str]] | None = None,
    retry_reason: str | None = None,
    failed_vcs: list[dict[str, Any]] | None = None,
    previous_vc_changes: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    state["waiting_for"] = []
    report_root = Path(str(state["report_root"]))
    round_id = _next_round_id(state, phase)
    attempt_id = f"{round_id}-attempt-{attempt_index}"
    if phase == "annotation":
        session = state.get("annotation_session")
        annotation_iteration = (
            int(session.get("iteration_count", 0)) + 1
            if isinstance(session, dict)
            else 1
        )
        paths = _annotation_paths(Path(str(state["run_root"])), annotation_iteration)
    else:
        paths = _round_paths(report_root, round_id)
        annotation_iteration = 0
    retry_failed_vcs = failed_vcs or []
    vc_change_history = previous_vc_changes or []
    target = state["target_files"]
    allowed = []
    if phase == "annotation":
        allowed = [target["c_file"]]
        if _formal_case_lib_is_active(state):
            allowed.append(target["formal_case_lib"])
        allowed.extend(target[key] for key in GENERATED_KEYS)
    else:
        allowed = [target["proof_manual_file"]]
    write_text(
        paths["input"],
        _render_agent_input(
            state,
            phase=phase,
            round_id=round_id,
            attempt_id=attempt_id,
            paths=paths,
            allowed_write_paths=allowed,
            previous_attempts=previous_attempts or [],
            required_lessons=required_lessons or [],
            attempt_index=attempt_index,
            annotation_iteration=annotation_iteration,
            feedback_sources=feedback_sources or [],
            retry_reason=retry_reason,
            failed_vcs=retry_failed_vcs,
            previous_vc_changes=vc_change_history,
        ),
    )
    if phase == "annotation":
        previous_plan: dict[str, Any] | None = None
        for previous in reversed(previous_attempts or []):
            raw_path = previous.get("plan") if isinstance(previous, dict) else None
            if not isinstance(raw_path, str) or not raw_path:
                continue
            candidate = _json_load(Path(raw_path), {})
            if isinstance(candidate, dict):
                previous_plan = candidate
                break
        if previous_plan is None:
            plan = _annotation_plan_template()
        else:
            plan = {
                "version": 2,
                "status": "planning",
                "function_specs": previous_plan["function_specs"],
                "loop_invariants": previous_plan["loop_invariants"],
                "new_predicates": previous_plan["new_predicates"],
                "vc_comparisons": [],
            }
        write_json(paths["plan"], plan)
    write_json(paths["report"], _agent_report_payload())
    if phase == "vc-checking":
        write_text(
            paths["output"],
            _vc_decision_summary_skeleton(),
        )
    attempt: dict[str, Any] = {
        "attempt_id": attempt_id,
        "round": round_id,
        "phase": phase,
        "status": "prepared",
        "report_directory": str(paths["directory"]),
        "input": str(paths["input"]),
        "report": str(paths["report"]),
        "output": str(paths["output"]),
        "allowed_write_paths": allowed,
        "compact_attempt_index": attempt_index,
        "created_at": _utc(),
    }
    if phase == "annotation":
        attempt["plan"] = str(paths["plan"])
        history = annotation_history_root(
            Path(str(state["run_root"]))
        ) / annotation_attempt_directory_name(annotation_iteration)
        attempt["annotation_history_directory"] = str(history)
        attempt["annotation_iteration"] = annotation_iteration
        attempt["failed_vcs"] = retry_failed_vcs
        attempt["feedback_sources"] = feedback_sources or []
        attempt["retry_reason"] = retry_reason
        attempt["before_snapshot"] = _archive_annotation_stage(
            state,
            attempt,
            "before",
            initializing=True,
        )
        session = state.get("annotation_session")
        if not isinstance(session, dict):
            session = {
                "session_id": f"{state['case']}-annotation-agent",
            }
            state["annotation_session"] = session
        session.update(
            {
                "status": attempt["status"],
                "current_attempt": attempt_id,
                "iteration_count": annotation_iteration,
            }
        )
    state["rounds"][round_id] = {"phase": phase, "current_attempt": attempt_id}
    state["attempts"][attempt_id] = attempt
    if phase == "annotation":
        attempt["input_sha256"] = _file_digest(paths["input"])
        if annotation_iteration == 1:
            state["next_actions"] = [
                {
                    "id": f"spawn-{attempt_id}",
                    "kind": "spawn-annotation-agent",
                    "phase": phase,
                    "session_id": state["annotation_session"]["session_id"],
                    "attempt_id": attempt_id,
                    "input": str(paths["input"]),
                    "report": str(paths["report"]),
                    "feedback_sources": [],
                }
            ]
        else:
            state["next_actions"] = [
                {
                    "id": f"append-{attempt_id}",
                    "kind": "append-annotation-agent",
                    "phase": phase,
                    "session_id": state["annotation_session"]["session_id"],
                    "attempt_id": attempt_id,
                    "input": str(paths["input"]),
                    "report": str(paths["report"]),
                    "feedback_sources": feedback_sources or [],
                }
            ]
    else:
        state["next_actions"] = [
            {
                "id": f"spawn-{attempt_id}",
                "kind": "spawn-attempt",
                "phase": phase,
                "attempt_id": attempt_id,
                "input": str(paths["input"]),
                "report": str(paths["report"]),
            }
        ]
    return attempt


def _init_vc_proving_attempt(state: dict[str, Any]) -> dict[str, Any]:
    state["waiting_for"] = []
    round_id = _next_round_id(state, "vc-proving")
    run_root = Path(str(state["run_root"]))
    report_directory = round_report_root(run_root, round_id)
    directory = fixed_path_under(
        run_root / round_id,
        run_root,
        label="vc-proving round directory",
    )
    directory.mkdir(parents=True, exist_ok=True)
    attempt = {
        "attempt_id": round_id,
        "round": round_id,
        "phase": VC_PROVING_PHASE,
        "status": "prepared",
        "directory": str(directory),
        "report_directory": str(report_directory),
        "base_manifest": str(directory / "base_manifest.json"),
        "group_workers_manifest": str(report_directory / "group_workers_manifest.json"),
        "proving_merged_result": str(report_directory / "proving_merged_result.json"),
        "groups": {},
        "priority_group_ids": [],
        "previous_proving_round": _previous_vc_proving_round(state),
        # The run-level value is already validated by init-run.  Copy it into
        # the proving attempt so scheduling remains sealed for the lifetime of
        # this round even if a later controller invocation uses other options.
        "max_parallel_group_workers": int(state["max_parallel_group_workers"]),
        "created_at": _utc(),
    }
    state["rounds"][round_id] = {"phase": VC_PROVING_PHASE, "current_attempt": round_id}
    state["attempts"][round_id] = attempt
    state["next_actions"] = [
        {
            "id": f"vc-proving-preparing-{round_id}",
            "kind": "main-owned-action",
            "action": "vc-proving-preparing",
            "round": round_id,
            "attempt_id": round_id,
        }
    ]
    return attempt


def _current_attempt(state: dict[str, Any], phase: str) -> dict[str, Any] | None:
    candidates = [
        item
        for item in state["attempts"].values()
        if item.get("phase") == phase
        and item.get("status") not in {"stale", "superseded"}
    ]
    return candidates[-1] if candidates else None


def _running_deliveries(state: dict[str, Any]) -> list[dict[str, str]]:
    running: list[dict[str, str]] = []
    for attempt in state.get("attempts", {}).values():
        if attempt.get("status") == "running":
            item = {
                "attempt_id": str(attempt["attempt_id"]),
                "status": "running",
            }
            if attempt.get("owner"):
                item["owner"] = str(attempt["owner"])
            running.append(item)
        for group_id, group_state in (attempt.get("groups") or {}).items():
            if not isinstance(group_state, dict):
                continue
            if group_state.get("status") != "running":
                continue
            item = {
                "attempt_id": f"{attempt['round']}:{group_id}",
                "status": "running",
            }
            if group_state.get("owner"):
                item["owner"] = str(group_state["owner"])
            running.append(item)
    return running


def _group_artifact_paths(
    group: dict[str, Any], *, expected: dict[str, Any] | None = None
) -> dict[str, Path]:
    directory = Path(str(group["directory"]))
    report = Path(str(group["report_directory"]))
    try:
        directory = fixed_path_under(
            directory,
            directory.parent,
            label="group artifact directory",
        )
        report = fixed_path_under(
            report,
            report.parent,
            label="group artifact report directory",
        )
        proof_manual = fixed_path_under(
            Path(str(group["proof_manual"])),
            directory,
            label="group proof manual artifact",
        )
        report_artifact = fixed_path_under(
            report / "group_worker_report.json",
            report,
            label="group worker report artifact",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    paths = {
        "report": report_artifact,
        "proof_manual": proof_manual,
    }
    if isinstance(expected, dict) and "output" in expected:
        try:
            paths[NOTES_ARTIFACT_ROLE] = fixed_path_under(
                report / GROUP_NOTES_FILENAME,
                report,
                label="group worker output artifact",
            )
        except SystemExit as exc:
            raise ValueError(str(exc)) from exc
    group_worker_lib = group.get("group_worker_lib")
    if isinstance(group_worker_lib, str) and group_worker_lib:
        try:
            paths["group_worker_lib"] = fixed_path_under(
                Path(group_worker_lib),
                directory,
                label="group worker lib artifact",
            )
        except SystemExit as exc:
            raise ValueError(str(exc)) from exc
    return paths


def _group_artifact_digests(
    group: dict[str, Any], *, expected: dict[str, Any] | None = None
) -> dict[str, str | None]:
    paths = _group_artifact_paths(group, expected=expected)
    owners = {
        "report": Path(str(group["report_directory"])),
        "output": Path(str(group["report_directory"])),
        "proof_manual": Path(str(group["directory"])),
        "group_worker_lib": Path(str(group["directory"])),
    }
    return {
        name: str(
            _stable_fixed_file_snapshot(
                path,
                owner=owners[name],
                label=f"sealed group {name}",
            )["sha256"]
        )
        for name, path in paths.items()
    }


def _group_artifact_seal_matches(group: dict[str, Any], expected: Any) -> bool:
    try:
        paths = _group_artifact_paths(
            group,
            expected=expected if isinstance(expected, dict) else None,
        )
    except (OSError, TypeError, ValueError):
        return False
    if not isinstance(expected, dict) or set(expected) != set(paths):
        return False
    try:
        current = _group_artifact_digests(group, expected=expected)
    except (OSError, TypeError, ValueError):
        return False
    return not any(value is None for value in current.values()) and current == expected


def _accepted_group_artifacts_are_sealed(
    attempt: dict[str, Any], groups: list[dict[str, Any]]
) -> bool:
    manifest_ids = {str(group["id"]) for group in groups}
    if not groups or _accepted_group_ids(attempt) != manifest_ids:
        return False
    for group in groups:
        group_state = attempt.get("groups", {}).get(str(group["id"]), {})
        if not isinstance(group_state, dict) or group_state.get("status") != "accepted":
            return False
        expected = group_state.get("accepted_artifact_sha256")
        if not _group_artifact_seal_matches(group, expected):
            return False
    return True


def _accepted_group_ids(attempt: dict[str, Any]) -> set[str]:
    return {
        str(group_id)
        for group_id, group_state in attempt.get("groups", {}).items()
        if isinstance(group_state, dict) and group_state.get("status") == "accepted"
    }


def _group_blocker_retry_phase(blockers: Any) -> str | None:
    """Route group blockers only by their machine class."""

    first = (
        blockers[0]
        if isinstance(blockers, list)
        and blockers
        and isinstance(blockers[0], dict)
        else None
    )
    if not isinstance(first, dict):
        return None
    failure_class = str(first.get("failure_class") or "")
    if failure_class in GROUP_VC_CHECKING_FAILURE_CLASSES:
        return "vc-checking"
    if failure_class == ANNOTATION_GAP_FAILURE_CLASS:
        return "annotation"
    return None


def _annotation_gap_feedback_records(
    attempt: dict[str, Any], manifest: dict[str, Any]
) -> list[dict[str, Any]]:
    """Return owner annotation gaps in accepted-plan/source order.

    The owner-authored blocker remains the semantic payload.  Group and
    witness provenance are derived from the accepted-plan projection in the
    sealed worker manifest, while the Markdown/JSON paths point back to the
    original group delivery rather than copying either artifact.
    """

    groups = {
        str(group.get("id") or ""): group
        for group in manifest.get("groups", [])
        if isinstance(group, dict) and group.get("id")
    }
    records: list[dict[str, Any]] = []
    for group_id in manifest.get("order", []):
        group_id = str(group_id)
        group_state = attempt.get("groups", {}).get(group_id, {})
        blockers = (
            group_state.get("blockers") if isinstance(group_state, dict) else None
        )
        blocker = (
            blockers[0]
            if isinstance(blockers, list)
            and len(blockers) == 1
            and isinstance(blockers[0], dict)
            else None
        )
        if (
            not isinstance(group_state, dict)
            or group_state.get("status") != "blocked"
            or not isinstance(blocker, dict)
            or blocker.get("failure_class") != ANNOTATION_GAP_FAILURE_CLASS
        ):
            continue
        group = groups.get(group_id)
        if not isinstance(group, dict):
            raise SystemExit(
                f"annotation-gap group is missing from the sealed manifest: {group_id}"
            )
        sealed_paths = _narrative_paths(
            _group_artifact_paths(group, expected=group_state.get("artifact_sha256"))
        )
        records.append(
            {
                "failure_class": str(blocker["failure_class"]),
                "kind": str(blocker["kind"]),
                "round": str(attempt["round"]),
                "group_id": group_id,
                "witnesses": [
                    str(witness.get("name") or "")
                    for witness in group.get("witnesses", [])
                    if isinstance(witness, dict) and witness.get("name")
                ],
                "vcs": [dict(item) for item in blocker["vcs"]],
                "message": str(blocker["message"]),
                "repair_boundary": str(blocker["repair_boundary"]),
                "evidence": [str(path) for path in sealed_paths.values()],
            }
        )
    return records


def _detect_group_artifact_drift(
    state: dict[str, Any], attempt: dict[str, Any], groups: list[dict[str, Any]]
) -> list[str]:
    """Turn post-validation edits into an explicit state transition."""

    accepted = _accepted_group_ids(attempt)
    by_id = {str(group["id"]): group for group in groups}
    integrity_errors: list[str] = []
    for group_id in sorted(accepted):
        group = by_id.get(str(group_id))
        group_state = attempt.get("groups", {}).get(str(group_id), {})
        if not isinstance(group, dict):
            integrity_errors.append(
                f"accepted group is absent from the sealed worker manifest: {group_id}"
            )
            continue
        sealed = group_state.get("accepted_artifact_sha256")
        try:
            paths = _group_artifact_paths(group, expected=sealed)
        except (OSError, TypeError, ValueError) as exc:
            integrity_errors.append(
                f"accepted group artifact topology is invalid: {group_id}: {exc}"
            )
            continue
        if not isinstance(sealed, dict) or set(sealed) != set(paths):
            integrity_errors.append(
                f"accepted group artifact seal fields differ from topology: {group_id}"
            )
            continue
        if any(
            not isinstance(digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            for digest in sealed.values()
        ):
            integrity_errors.append(
                f"accepted group artifact seal digest is invalid: {group_id}"
            )
            continue
        try:
            current = _group_artifact_digests(group, expected=sealed)
        except (OSError, TypeError, ValueError) as exc:
            current = {name: None for name in paths}
            integrity_errors.append(
                f"accepted group artifact cannot be read safely: {group_id}: {exc}"
            )
        if current == sealed:
            continue
        changed = next(
            (
                name
                for name in sorted(set(sealed) | set(current))
                if sealed.get(name) != current.get(name)
            ),
            "unknown",
        )
        group_state["status"] = "returned"
        group_state["validation_reason"] = "artifact-drift-after-validation"
        group_state["validation_errors"] = [
            f"accepted group artifact changed after validation: {changed}"
        ]
        group_state["artifact_sha256"] = {
            key: value for key, value in current.items() if value is not None
        }
        _append_event(
            Path(str(state["run_root"])),
            state,
            "artifact-drift-after-validation",
            round=attempt["round"],
            group_id=str(group_id),
            changed_artifact=changed,
        )
    return integrity_errors


def _detect_annotation_gap_artifact_drift(
    state: dict[str, Any], attempt: dict[str, Any], groups: list[dict[str, Any]]
) -> None:
    """Reject edits made after an annotation-gap group was finalized."""

    by_id = {str(group["id"]): group for group in groups}
    for group_id in [str(group["id"]) for group in groups]:
        group_state = attempt.get("groups", {}).get(group_id, {})
        blockers = (
            group_state.get("blockers") if isinstance(group_state, dict) else None
        )
        blocker = (
            blockers[0]
            if isinstance(blockers, list)
            and len(blockers) == 1
            and isinstance(blockers[0], dict)
            else None
        )
        if (
            not isinstance(group_state, dict)
            or group_state.get("status") != "blocked"
            or not isinstance(blocker, dict)
            or blocker.get("failure_class") != ANNOTATION_GAP_FAILURE_CLASS
        ):
            continue
        group = by_id[group_id]
        sealed = group_state.get("artifact_sha256")
        if _group_artifact_seal_matches(group, sealed):
            continue
        message = (
            "annotation-gap group artifact changed after terminal delivery: "
            + group_id
        )
        group_state["status"] = "invalid-report"
        group_state["validation_errors"] = [message]
        _append_event(
            Path(str(state["run_root"])),
            state,
            "annotation-gap-artifact-drift",
            round=str(attempt["round"]),
            group_id=group_id,
        )


def _sync_group_actions(state: dict[str, Any], attempt: dict[str, Any]) -> None:
    if attempt.get("status") != "groups-ready":
        state["next_actions"] = []
        state["waiting_for"] = []
        return
    try:
        attempt_paths = _validated_proving_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        state["next_actions"] = []
        state["waiting_for"] = _running_deliveries(state)
        state["current_blockers"] = [
            {
                "failure_class": "vc-proving-attempt-path-topology",
                "message": str(exc),
            }
        ]
        return
    manifest_path = attempt_paths["group_workers_manifest"]
    base_path = attempt_paths["base_manifest"]
    pinned_errors: list[str] = []
    for label, path, expected in (
        (
            "group_workers_manifest",
            manifest_path,
            str(attempt.get("group_workers_manifest_sha256") or ""),
        ),
        (
            "base_manifest",
            base_path,
            str(attempt.get("base_manifest_sha256") or ""),
        ),
    ):
        if not path.is_file() or not expected or _file_digest(path) != expected:
            pinned_errors.append(f"{label} changed after vc-proving preparation")
    if pinned_errors:
        state["next_actions"] = []
        state["waiting_for"] = _running_deliveries(state)
        state["current_blockers"] = [
            {
                "failure_class": "vc-proving-controller-artifact-drift",
                "message": pinned_errors[0],
            }
        ]
        return
    # A previous preparation/check failure is no longer current once every
    # pinned controller input has been revalidated. Branches below install a
    # fresh blocker when they intentionally stop dispatch.
    state["current_blockers"] = []
    try:
        manifest = resolve_group_workers_manifest(
            manifest_path,
            main_root=Path(str(state["main_root"])),
            expected_run_root=Path(str(state["run_root"])),
            expected_round=str(attempt["round"]),
        )
    except (OSError, TypeError, ValueError, SystemExit) as exc:
        state["current_blockers"] = [
            {
                "failure_class": "vc-proving-controller-artifact-drift",
                "message": str(exc),
            }
        ]
        state["next_actions"] = []
        state["waiting_for"] = _running_deliveries(state)
        return
    groups = (
        manifest.get("groups")
        if isinstance(manifest, dict) and isinstance(manifest.get("groups"), list)
        else []
    )
    drift_integrity_errors = _detect_group_artifact_drift(state, attempt, groups)
    if drift_integrity_errors:
        state["current_blockers"] = [
            {
                "failure_class": "accepted-group-artifact-seal-integrity",
                "message": drift_integrity_errors[0],
                "error_count": len(drift_integrity_errors),
            }
        ]
        state["next_actions"] = []
        state["waiting_for"] = _running_deliveries(state)
        return
    _detect_annotation_gap_artifact_drift(state, attempt, groups)
    accepted = _accepted_group_ids(attempt)
    manifest_group_ids = {str(group["id"]) for group in groups}
    if accepted == manifest_group_ids and (
        not groups or _accepted_group_artifacts_are_sealed(attempt, groups)
    ):
        state["next_actions"] = [
            {
                "id": f"vc-proving-verify-{attempt['round']}",
                "kind": "main-owned-action",
                "action": "vc-proving-verify",
                "round": attempt["round"],
                "attempt_id": attempt["attempt_id"],
            }
        ]
        state["waiting_for"] = []
        return
    validation_actions: list[dict[str, Any]] = []
    for group_id in manifest.get("order", []):
        group_state = attempt.get("groups", {}).get(str(group_id), {})
        if group_state.get("status") == "returned":
            delivery = group_state.get("delivery")
            if not isinstance(delivery, dict) or not delivery.get("owner"):
                raise SystemExit(
                    f"returned group has no delivery owner: {attempt['round']}:{group_id}"
                )
            validation_actions.append(
                {
                    "id": f"finalize-{attempt['round']}-{group_id}",
                    "kind": "main-owned-action",
                    "action": "finalize-delivery",
                    "attempt_id": f"{attempt['round']}:{group_id}",
                    "owner": str(delivery["owner"]),
                    **(
                        {"reason": "artifact-drift-after-validation"}
                        if attempt["groups"][str(group_id)].get("validation_reason")
                        == "artifact-drift-after-validation"
                        else {}
                    ),
                }
            )
    pending_promotion = state.get("public_helper_promotion_transaction")
    if isinstance(pending_promotion, dict) and str(
        pending_promotion.get("round") or ""
    ) == str(attempt["round"]):
        owner_attempt = (
            f"{attempt['round']}:{pending_promotion.get('group_id') or ''!s}"
        )
        recovery_actions = [
            action
            for action in validation_actions
            if action.get("attempt_id") == owner_attempt
        ]
        if recovery_actions:
            # The append receipt belongs to one already checked group. A
            # sibling validation cannot consume it and would deterministically
            # fail until the owner reconciles the before/after pool digest.
            # Publish only the owner's existing finalize action for this short
            # recovery window; normal independent scheduling resumes as soon
            # as that validation commits and removes the receipt.
            validation_actions = recovery_actions
    running = sum(
        1 for item in attempt["groups"].values() if item.get("status") == "running"
    )
    failed_group_ids = [
        str(group_id)
        for group_id in manifest.get("order", [])
        if attempt.get("groups", {}).get(str(group_id), {}).get("status")
        in {
            "blocked",
            "invalid-report",
            "stale",
            "compact-error-retry-exhausted",
        }
    ]
    annotation_gap_records = _annotation_gap_feedback_records(attempt, manifest)
    annotation_gap_group_ids = {
        str(record["group_id"]) for record in annotation_gap_records
    }
    priority_group_ids = {
        str(group_id) for group_id in attempt["priority_group_ids"]
    }
    priority_gap_records = [
        record
        for record in annotation_gap_records
        if str(record["group_id"]) in priority_group_ids
    ]
    if priority_gap_records:
        state["waiting_for"] = _running_deliveries(state)
        if validation_actions:
            state["next_actions"] = validation_actions
            return
        if running:
            state["next_actions"] = []
            return
        state["current_blockers"] = priority_gap_records
        state["next_actions"] = [
            {
                "id": f"annotation-feedback-{attempt['round']}-priority",
                "kind": "main-owned-action",
                "action": "retry-round",
                "phase": "annotation",
                "reason": "priority-group-annotation-gaps",
                "previous_attempt": str(attempt["round"]),
            }
        ]
        state["waiting_for"] = []
        return
    blocking_group_ids = [
        group_id
        for group_id in failed_group_ids
        if group_id not in annotation_gap_group_ids
    ]
    if blocking_group_ids:
        state["waiting_for"] = _running_deliveries(state)
        if validation_actions:
            state["next_actions"] = validation_actions
            return
        if running:
            state["next_actions"] = []
            return
        stale_group = next(
            (
                group_id
                for group_id in blocking_group_ids
                if attempt["groups"][group_id].get("status") == "stale"
            ),
            None,
        )
        if stale_group is not None:
            # Current-file drift invalidates the accepted annotation all groups
            # share.  Do not start the remaining prepared workers and do not
            # misroute this as a plan/report retry: return the machine-detected
            # drift through the existing persistent annotation feedback path.
            drift_receipt = attempt["groups"][stale_group].get("file_drift")
            state["current_blockers"] = [
                drift_receipt
                if isinstance(drift_receipt, dict)
                else {
                    "failure_class": "current-file-drift",
                    "round": str(attempt["round"]),
                    "group_id": stale_group,
                    "message": str(
                        attempt["groups"][stale_group].get("stale_reason")
                        or "group became stale after current-file drift"
                    ),
                }
            ]
            state["next_actions"] = [
                {
                    "id": f"annotation-feedback-{attempt['round']}-{stale_group}",
                    "kind": "main-owned-action",
                    "action": "retry-round",
                    "phase": "annotation",
                    "reason": "group-worker-stale",
                    "previous_attempt": f"{attempt['round']}:{stale_group}",
                }
            ]
            return
        compact_exhausted_group = next(
            (
                group_id
                for group_id in blocking_group_ids
                if attempt["groups"][group_id].get("status")
                == "compact-error-retry-exhausted"
            ),
            None,
        )
        if compact_exhausted_group is not None:
            group_state = attempt["groups"][compact_exhausted_group]
            blocker = next(
                (
                    item
                    for item in group_state.get("blockers", [])
                    if isinstance(item, dict)
                ),
                {
                    "failure_class": "compact-error-retry-exhausted",
                    "round": str(attempt["round"]),
                    "group_id": compact_exhausted_group,
                },
            )
            state["next_actions"] = []
            state["current_blockers"] = [blocker]
            return
        invalid_group = next(
            (
                group_id
                for group_id in blocking_group_ids
                if attempt["groups"][group_id].get("status") == "invalid-report"
            ),
            None,
        )
        if invalid_group is not None:
            group = next(
                item for item in groups if str(item.get("id")) == invalid_group
            )
            group_state = attempt["groups"][invalid_group]
            sealed = group_state.get("artifact_sha256")
            drifted = not _group_artifact_seal_matches(group, sealed)
            validation_errors = group_state.get("validation_errors")
            message = (
                str(validation_errors[0])
                if isinstance(validation_errors, list) and validation_errors
                else "invalid group report"
            )
            state["next_actions"] = []
            state["current_blockers"] = [
                {
                    "failure_class": "invalid-report",
                    "round": str(attempt["round"]),
                    "group_id": invalid_group,
                    "message": message,
                    "sealed_artifact_drift": drifted,
                }
            ]
            return
        blocked_group = next(
            (
                group_id
                for group_id in blocking_group_ids
                if attempt["groups"][group_id].get("status") == "blocked"
            ),
            None,
        )
        if blocked_group is not None:
            group_blockers = attempt["groups"][blocked_group].get("blockers", [])
            retry_phase = _group_blocker_retry_phase(group_blockers)
            if retry_phase is None:
                state["next_actions"] = []
                state["current_blockers"] = [
                    {
                        "failure_class": "group-blocked",
                        "round": str(attempt["round"]),
                        "group_id": blocked_group,
                        "blockers": group_blockers,
                    }
                ]
                return
            plan_failure = retry_phase == "vc-checking"
            if plan_failure:
                first_blocker = (
                    group_blockers[0]
                    if isinstance(group_blockers, list) and group_blockers
                    else "group reported an unusable vc plan or proof route"
                )
                state["current_blockers"] = [
                    {
                        "failure_class": "group-vc-plan-blocked",
                        "round": str(attempt["round"]),
                        "group_id": blocked_group,
                        "first_blocker": first_blocker,
                        "blocker_count": (
                            len(group_blockers)
                            if isinstance(group_blockers, list)
                            else 0
                        ),
                    },
                    *annotation_gap_records,
                ]
            state["next_actions"] = [
                {
                    "id": f"{retry_phase}-feedback-{attempt['round']}-{blocked_group}",
                    "kind": "main-owned-action",
                    "action": "retry-round",
                    "phase": retry_phase,
                    "reason": (
                        "group-worker-vc-plan-blocked"
                        if plan_failure
                        else "group-worker-blocked"
                    ),
                    "previous_attempt": (
                        str(
                            state.get("accepted_rounds", {})
                            .get("vc-checking", {})
                            .get("attempt_id")
                            or ""
                        )
                        if plan_failure
                        else f"{attempt['round']}:{blocked_group}"
                    ),
                }
            ]
        return
    if annotation_gap_group_ids and (
        accepted | annotation_gap_group_ids
    ) == manifest_group_ids:
        # Annotation gaps are outside every group owner's write boundary, but
        # they do not cancel sibling work. Only after every group reaches a
        # terminal state does the controller publish one annotation retry.
        annotation_gap_records = _annotation_gap_feedback_records(attempt, manifest)
        if {
            str(record["group_id"]) for record in annotation_gap_records
        } != annotation_gap_group_ids:
            raise SystemExit(
                "annotation-gap feedback changed while sealing the proving round"
            )
        state["current_blockers"] = annotation_gap_records
        state["next_actions"] = [
            {
                "id": f"annotation-feedback-{attempt['round']}",
                "kind": "main-owned-action",
                "action": "retry-round",
                "phase": "annotation",
                "reason": "group-worker-annotation-gaps",
                "previous_attempt": str(attempt["round"]),
            }
        ]
        state["waiting_for"] = []
        _append_event(
            Path(str(state["run_root"])),
            state,
            "group-annotation-gaps-aggregated",
            round=str(attempt["round"]),
            group_ids=[
                str(record["group_id"]) for record in annotation_gap_records
            ],
            blocker_count=len(annotation_gap_records),
        )
        return
    actions: list[dict[str, Any]] = []
    configured_limit = int(attempt["max_parallel_group_workers"])
    if configured_limit < 1:
        raise SystemExit("max_parallel_group_workers must remain positive")
    # The attempt value is the scheduling authority.  A second hard cap used
    # to silently reduce valid run configuration back to three workers, which
    # left available agent slots idle and contradicted the persisted field.
    available = max(0, configured_limit - running)
    by_id = {str(group["id"]): group for group in groups}
    priority_pending = priority_group_ids - accepted
    dispatch_ids = [
        str(group_id)
        for group_id in manifest.get("dispatch_order", manifest.get("order", []))
        if not priority_pending or str(group_id) in priority_group_ids
    ]
    for group_id in dispatch_ids:
        if available <= 0:
            break
        group = by_id.get(str(group_id))
        if not group or str(group_id) in accepted:
            continue
        status = attempt["groups"].get(str(group_id), {}).get("status")
        if status in {
            "running",
            "returned",
            "blocked",
            "stale",
            "invalid-report",
        }:
            continue
        attempt["groups"].setdefault(
            str(group_id), {"status": "prepared", "attempt_index": 1}
        )
        report_dir = Path(str(group["report_directory"]))
        action_kind = (
            "append-group-worker"
            if status == "repair-prepared"
            else "spawn-group-worker"
        )
        repair_index = int(
            attempt["groups"].get(str(group_id), {}).get("repair_index", 0)
        )
        actions.append(
            {
                "id": (
                    f"append-{attempt['round']}-{group_id}-repair-{repair_index}"
                    if action_kind == "append-group-worker"
                    else f"spawn-{attempt['round']}-{group_id}"
                ),
                "kind": action_kind,
                "phase": VC_PROVING_PHASE,
                "attempt_id": f"{attempt['round']}:{group_id}",
                "round": attempt["round"],
                "group_id": str(group_id),
                "input": str(report_dir / "group_worker_input.md"),
                "report": str(report_dir / "group_worker_report.json"),
            }
        )
        available -= 1
    state["next_actions"] = [*validation_actions, *actions]
    state["waiting_for"] = _running_deliveries(state)


def _dune_gate_errors(state: dict[str, Any]) -> list[str]:
    return dune_preparation_receipt_errors(
        workspace_root=Path(str(state["main_root"])),
        receipt=(
            state.get("dune_preparation")
            if isinstance(state.get("dune_preparation"), dict)
            else None
        ),
    )


def _queue_dune_gate(state: dict[str, Any]) -> None:
    state["phase"] = "dune-build"
    state["next_actions"] = [_preparation_action(state)]
    state["waiting_for"] = []


def _target_witnesses(state: dict[str, Any]) -> list[str]:
    try:
        obligations = _manual_obligations(state)
    except (OSError, UnicodeError, ValueError) as exc:
        raise SystemExit(f"current proof manual cannot be parsed: {exc}") from exc
    return [str(item) for item in obligations["top_level"]]


def _proving_feedback_attempt_id(state: dict[str, Any]) -> str:
    vc_attempt = str(
        state.get("accepted_rounds", {})
        .get("vc-checking", {})
        .get("attempt_id")
        or ""
    )
    if vc_attempt:
        return vc_attempt
    if _target_witnesses(state):
        raise SystemExit(
            "vc-proving has manual witnesses but no accepted vc-checking attempt"
        )
    annotation_attempt = str(
        state.get("accepted_rounds", {})
        .get("annotation", {})
        .get("attempt_id")
        or ""
    )
    if not annotation_attempt:
        raise SystemExit(
            "vc-proving without manual witnesses has no accepted annotation attempt"
        )
    return annotation_attempt


def _advance_after_dune_build(state: dict[str, Any]) -> None:
    if _target_witnesses(state):
        state["phase"] = "vc-checking"
        _init_round_attempt(state, phase="vc-checking")
        return

    report_root = Path(str(state["report_root"]))
    plan_path = fixed_path_under(
        report_root / "group_plan.json",
        report_root,
        label="empty group plan",
    )
    write_json(plan_path, {"groups": []})
    state["accepted_rounds"]["vc-checking"] = {
        "group_plan": str(plan_path),
        "group_plan_sha256": _file_digest(plan_path),
        "proof_manual_sha256": _proof_manual_sha256(state),
    }
    state["phase"] = VC_PROVING_PHASE
    _init_vc_proving_attempt(state)
    _append_event(
        Path(str(state["run_root"])),
        state,
        "vc-checking-skipped",
        witness_count=0,
    )


def _queue_pre_vc_annotation_drift(
    state: dict[str, Any], errors: list[str]
) -> None:
    attempt_id = str(
        state.get("accepted_rounds", {})
        .get("annotation", {})
        .get("attempt_id")
        or ""
    )
    if not attempt_id:
        raise SystemExit(
            "pre-VC current-file drift has no accepted annotation attempt"
        )
    blocker = {
        "failure_class": "current-file-drift",
        "action": "dune-build",
        "message": errors[0],
        "error_count": len(errors),
        "detected_at": _utc(),
    }
    state["current_blockers"] = [blocker]
    state["next_actions"] = [
        {
            "id": "annotation-feedback-dune-build",
            "kind": "main-owned-action",
            "action": "retry-round",
            "phase": "annotation",
            "reason": "dune-preparation-file-drift",
            "previous_attempt": attempt_id,
        }
    ]


def step(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    from controller_control import run_control_record, run_is_paused

    if run_is_paused(state):
        control = run_control_record(state)
        print(
            json.dumps(
                {
                    "phase": state["phase"],
                    "status": "paused",
                    "next_actions": [],
                    "waiting_for": [
                        {
                            "phase": str(state["phase"]),
                            "status": "paused",
                            "reason": str(control.get("reason") or ""),
                        }
                    ],
                    "run_control": control,
                },
                indent=2,
            )
        )
        return 0
    state["waiting_for"] = []
    phase = state["phase"]
    pending_retry = any(
        item.get("kind") == "main-owned-action" and item.get("action") == "retry-round"
        for item in state.get("next_actions", [])
        if isinstance(item, dict)
    )
    parent_result_drift = next(
        (
            item.get("parent_result_artifact_drift")
            for item in state.get("attempts", {}).values()
            if isinstance(item, dict)
            and item.get("phase") == VC_PROVING_PHASE
            and isinstance(item.get("parent_result_artifact_drift"), dict)
        ),
        None,
    )
    # A main-owned retry action is an explicit state transition awaiting the
    # caller. Re-stepping must not infer and publish a fresh phase attempt over
    # it, especially after a file gate has just routed back to annotation.
    if isinstance(parent_result_drift, dict):
        # A completed parent result whose digest no longer matches cannot be
        # rerun from a terminal proving state and cannot authorize final apply.
        # Preserve the compact blocker across arbitrary repeated step calls.
        state["next_actions"] = []
        state["current_blockers"] = [parent_result_drift]
    elif pending_retry:
        pass
    elif phase == "intake":
        state["phase"] = "annotation"
        _init_round_attempt(state, phase="annotation")
    elif phase == "annotation":
        if "annotation" in state["accepted_rounds"]:
            file_errors = _current_files_errors(state)
            if file_errors:
                state["phase"] = "dune-build"
                _queue_pre_vc_annotation_drift(state, file_errors)
            elif _dune_gate_errors(state):
                _queue_dune_gate(state)
            else:
                _advance_after_dune_build(state)
        elif _current_attempt(state, "annotation") is None:
            _init_round_attempt(state, phase="annotation")
    elif phase == "dune-build":
        file_errors = _current_files_errors(state)
        if file_errors:
            _queue_pre_vc_annotation_drift(state, file_errors)
        else:
            gate_errors = _dune_gate_errors(state)
            if gate_errors:
                receipt = state.get("dune_preparation")
                if (
                    isinstance(receipt, dict)
                    and receipt.get("status") == "passed"
                ):
                    makefile_mode = receipt.get("build_mode") == "makefile"
                    receipt["status"] = "stale"
                    receipt["first_failure"] = {
                        "category": "freshness",
                        "kind": (
                            "makefile-source-drift"
                            if makefile_mode
                            else "dune-source-drift"
                        ),
                        "message": gate_errors[0],
                        "repair": (
                            "Rerun the same exact Makefile target preparation."
                            if makefile_mode
                            else "Rerun the same exact Dune target preparation."
                        ),
                    }
                    _append_event(
                        run_root,
                        state,
                        "dune-preparation-stale",
                        first_error=gate_errors[0],
                    )
                _queue_dune_gate(state)
            else:
                state["current_blockers"] = []
                _advance_after_dune_build(state)
    elif phase == "vc-checking":
        if "vc-checking" in state["accepted_rounds"]:
            state["phase"] = VC_PROVING_PHASE
            _init_vc_proving_attempt(state)
        elif _current_attempt(state, "vc-checking") is None:
            _init_round_attempt(state, phase="vc-checking")
    elif phase == VC_PROVING_PHASE:
        attempt = _current_attempt(state, VC_PROVING_PHASE)
        if attempt is None:
            attempt = _init_vc_proving_attempt(state)
        elif attempt["status"] == "groups-ready":
            _sync_group_actions(state, attempt)
        elif attempt["status"] == "parent-verify-failed":
            retry_phase = (
                "vc-checking" if _target_witnesses(state) else "annotation"
            )
            state["next_actions"] = [
                {
                    "id": f"{retry_phase}-retry-{attempt['round']}",
                    "kind": "main-owned-action",
                    "action": "retry-round",
                    "phase": retry_phase,
                    "reason": "vc-proving-parent-failed",
                    "previous_attempt": _proving_feedback_attempt_id(state),
                }
            ]
        elif attempt["status"] == "verified":
            state["phase"] = "final-candidate-apply"
            state["next_actions"] = [
                {
                    "id": "final-candidate-apply",
                    "kind": "main-owned-action",
                    "action": "final-apply",
                }
            ]
    elif phase == "final-candidate-apply":
        final_apply_state = state.get("final_apply")
        final_apply_status = (
            final_apply_state.get("status")
            if isinstance(final_apply_state, dict)
            else None
        )
        if final_apply_status in {"blocked", "rollback-failed"}:
            state["next_actions"] = []
        else:
            state["next_actions"] = [
                {
                    "id": "final-candidate-apply",
                    "kind": "main-owned-action",
                    "action": "final-apply",
                }
            ]
    elif phase == "final-check":
        final_apply_state = state.get("final_apply")
        final_apply_status = (
            final_apply_state.get("status")
            if isinstance(final_apply_state, dict)
            else None
        )
        if final_apply_status == "passed":
            state["next_actions"] = [
                {
                    "id": "final-check",
                    "kind": "main-owned-action",
                    "action": "final-check",
                }
            ]
        elif final_apply_status == "rolled-back":
            state["phase"] = "final-candidate-apply"
            state["next_actions"] = [
                {
                    "id": "final-candidate-apply",
                    "kind": "main-owned-action",
                    "action": "final-apply",
                }
            ]
        else:
            state["next_actions"] = []
    elif phase == "done":
        state["next_actions"] = []
        state["waiting_for"] = []
    if not state.get("next_actions") and state.get("phase") != "done":
        running = _running_deliveries(state)
        state["waiting_for"] = running or [
            {
                "phase": str(state["phase"]),
                "status": (
                    "blocked" if state.get("current_blockers") else "awaiting-step"
                ),
            }
        ]
    _append_event(
        run_root,
        state,
        "controller-step",
        actions=[item["id"] for item in state["next_actions"]],
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "phase": state["phase"],
                "next_actions": hydrate_actions(
                    state, state.get("next_actions", [])
                ),
                "waiting_for": hydrate_waiting_deliveries(
                    state, state.get("waiting_for", [])
                ),
                **(
                    {"current_blockers": state["current_blockers"]}
                    if state.get("current_blockers")
                    else {}
                ),
            },
            indent=2,
        )
    )
    return 0


def _delivery_message(action: dict[str, Any]) -> str:
    """Render the agent message used by the atomic claim operation."""

    if action.get("kind") not in {
        "spawn-attempt",
        "spawn-group-worker",
        "append-group-worker",
        "spawn-annotation-agent",
        "append-annotation-agent",
    }:
        raise ValueError(f"action is not an agent delivery: {action.get('id')}")
    if action["kind"] in {"spawn-group-worker", "append-group-worker"}:
        from path_utils import group_worker_append_message, group_worker_spawn_message

        return (
            group_worker_append_message(action["input"], action["report"])
            if action["kind"] == "append-group-worker"
            else group_worker_spawn_message(action["input"], action["report"])
        )
    if action["kind"] == "spawn-annotation-agent":
        return _annotation_spawn_message(action)
    if action["kind"] == "append-annotation-agent":
        return _annotation_append_message(action)
    return _spawn_message(Path(str(action["input"])), Path(str(action["report"])))
