#!/usr/bin/env python3
"""Round creation, compact Markdown handoffs, stepping, and group scheduling."""

from __future__ import annotations

import argparse
import json
import re
import shlex
from pathlib import Path
from typing import Any

from path_utils import annotation_attempt_report_root, annotation_history_root, round_report_root, write_json, write_text

from controller_state import (
    GENERATED_KEYS,
    _append_event,
    _archive_annotation_stage,
    _ensure_formal_case_lib_seed,
    _file_digest,
    _json_load,
    _load_state,
    _run_root_from_id,
    _save_state,
    _source_version_for_state,
    _utc,
)


DEFAULT_MAX_PARALLEL_GROUP_WORKERS = 4
VC_PROVING_PHASE = "vc-proving-preparing"
MAIN_SUMMARY_MARKER = "<!-- MAIN_AGENT:"
ANNOTATION_SUMMARY_HEADINGS = (
    "Main-agent blocker conclusion",
    "Evidence and causal analysis",
    "Reflection on the previous annotation attempt",
    "Required annotation repair",
    "Scope decision",
)


def _round_paths(report_root: Path, round_id: str) -> dict[str, Path]:
    directory = report_root / "rounds" / round_id
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
        f"Tell it to read {action['input']} completely, including both annotation skills and the relevant "
        f"examples selected there, then write the terminal result to {action['report']}. "
        "Do not close or replace this agent after it returns; controller acceptance is separate."
    )


def _annotation_append_message(action: dict[str, Any]) -> str:
    feedback = ", ".join(
        str(path)
        for item in action.get("feedback_sources", [])
        for path in (item.get("markdown"), item.get("json"))
        if path
    )
    broader = (
        " This is a repeated repair: explicitly consider redesigning the mathematical spec, function contracts, "
        "and invariants together instead of applying another local patch."
        if action.get("consider_broader_refactor")
        else ""
    )
    return (
        f"Append this task to the existing annotation agent session {action['session_id']}; do not spawn a new agent. "
        f"Before editing, reload .agents/skills/annotation-filling/SKILL.md and "
        f".agents/skills/annotation-checking/SKILL.md completely, then read the main-agent blocker summary and "
        f"repair handoff {action['input']} plus its original blocker evidence ({feedback}). "
        f"Revise the current main-root formal C annotation and formal_case_lib, "
        f"rerun the exact checks, and write the terminal result to {action['report']}."
        + broader
    )


def _rules_source(phase: str) -> list[str]:
    result = [
        ".agents/skills/verification-orchestrator/SKILL.md",
        ".agents/skills/verification-orchestrator/docs/phase-handoff-report.md",
        ".agents/skills/verification-orchestrator/docs/path-configuration.md",
    ]
    if phase == "annotation":
        result.extend(
            [
                ".agents/skills/annotation-filling/SKILL.md",
                ".agents/skills/annotation-checking/SKILL.md",
            ]
        )
    else:
        result.append(".agents/skills/vc-checking/SKILL.md")
    return result


def _controller_command(state: dict[str, Any], command: str, *args: str) -> str:
    controller = Path(str(state["main_root"])) / ".agents" / "skills" / "verification-orchestrator" / "scripts" / "controller.py"
    argv = [
        "python3",
        str(controller),
        "--main-root",
        str(state["main_root"]),
        command,
        "--run",
        str(state["run_id"]),
        *args,
    ]
    return shlex.join(argv)


def _agent_report_payload(phase: str, source_goal_version: str | None = None) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema_version": "qcp-agent-report/v3",
        "status": "pending",
        "blockers": [],
    }
    if phase == "annotation":
        payload.update(
            {
                "changed_files": [],
                "checks": {
                    "symexec": "pending",
                    "formal_case_lib": "pending",
                    "annotation_checking": "pending",
                },
            }
        )
    else:
        payload["source_goal_version"] = source_goal_version
    return payload


def _format_list(items: list[str], *, empty: str = "none") -> str:
    return "\n".join(f"- `{item}`" for item in items) if items else f"- {empty}"


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
    return "\n".join(lines) if lines else "- Infer a conservative mathematical specification from the target C file."


def _main_summary_prompt(instruction: str) -> str:
    return f"{MAIN_SUMMARY_MARKER} {instruction} -->"


def _render_annotation_block_summary_template(
    state: dict[str, Any],
    *,
    round_id: str,
    attempt_id: str,
    paths: dict[str, Path],
    source_version: str,
    allowed_write_paths: list[str],
    previous_attempts: list[dict[str, Any]],
    required_lessons: list[dict[str, Any]],
    annotation_iteration: int,
    feedback_sources: list[dict[str, str]],
    retry_reason: str,
) -> str:
    target = state["target_files"]
    session = state.get("annotation_session")
    session_id = str(session["session_id"]) if isinstance(session, dict) else f"{state['case']}-annotation-agent"
    source_lines = (
        "\n".join(
            f"- `{item['phase']}` / `{item['attempt_id']}`: Markdown `{item['markdown']}`; JSON `{item['json']}`"
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
    controller_evidence = (
        "\n".join(f"- {item.get('must_address', item)}" for item in required_lessons)
        or "- No additional controller evidence."
    )
    broader_rule = (
        "This is the third or later annotation iteration. The scope decision must reassess the mathematical spec, "
        "function contracts, loop invariants, assertions, and call instantiations together and propose a broader "
        "redesign when the prior local design is the cause."
        if annotation_iteration >= 3
        else "Choose local repair or broader redesign from the evidence, and justify the boundary."
    )
    rules = _format_list(_rules_source("annotation"))
    symexec = _controller_command(state, "symexec", "--round", round_id)
    coq = _controller_command(state, "coq-check", "--round", round_id, "--target-kind", "formal-case-lib")
    checking_start = _controller_command(
        state, "timing-stage", "--round", round_id, "--stage", "annotation-checking", "--event", "start"
    )
    checking_finish = _controller_command(
        state, "timing-stage", "--round", round_id, "--stage", "annotation-checking", "--event", "finish"
    )
    return f"""# Annotation blocker summary and repair handoff

This is annotation iteration {annotation_iteration} in the run's single persistent annotation-agent session. The controller generated the factual sections and template; the main agent must read the original evidence and replace every `MAIN_AGENT` comment with a concrete summary before running `annotation-summary-ready`. Do not change controller-owned paths, versions, evidence references, or commands.

## Assignment

- Session: `{session_id}`
- Round: `{round_id}`
- Attempt: `{attempt_id}`
- Retry reason: `{retry_reason}`
- Main root: `{state['main_root']}`
- `source_version`: `{source_version}`
- Terminal report: `{paths['report']}`
- Human notes: `{paths['output']}`

## Target files

- C: `{target['c_file']}`
- `formal_case_lib`: `{target['formal_case_lib']}`
- Manual: `{target['proof_manual_file']}`
- Goal/auto/check: `{target['goal_file']}`, `{target['proof_auto_file']}`, `{target['goal_check_file']}`
- Diagnostics: `{target['proof_diagnostics_file']}`, `{target['diagnostics_snapshot']}`

## Original blocker evidence

{source_lines}

Previous annotation attempt artifacts:

{prior_lines}

Controller-recorded blocker details:

{controller_evidence}

## Main-agent blocker conclusion

{_main_summary_prompt('State the primary failure, the blocked witness/check, and why this requires another annotation iteration. Distinguish annotation/spec defects from proof-only or tooling failures.')}

## Evidence and causal analysis

{_main_summary_prompt('Cite the decisive facts from the original Markdown/JSON or controller main-check evidence. Trace the failure to concrete specs, contracts, invariants, assertions, or call instantiations; separate symptoms from the root cause.')}

## Reflection on the previous annotation attempt

{_main_summary_prompt('Explain which earlier assumption or repair strategy was inadequate, what useful part should be preserved, and what the annotation agent must not repeat.')}

## Required annotation repair

{_main_summary_prompt('Give an actionable repair objective, affected formal locations, constraints that must remain true, and exact success criteria for symexec, formal_case_lib, and annotation-checking.')}

## Controller scope requirement

{broader_rule}

## Scope decision

{_main_summary_prompt('Choose the repair scope and justify it against the causal evidence and the controller scope requirement above.')}

## Rules to reload

The annotation agent must completely reload both annotation skills on every appended iteration, then follow all linked rules and inspect the original blocker evidence above. The main-agent summary prioritizes the repair but does not replace the original evidence or current main-root files.

{rules}

## Writable formal paths

{_format_list(allowed_write_paths)}

Generated files may change only through the exact symbolic-execution command below.

## Commands

```text
{symexec}
{coq}
{checking_start}
{checking_finish}
```

Run the timing-stage start command immediately before invoking annotation-checking, and run the finish command only
after its review/repair loop completes. These commands measure the whole annotation-checking stage; they do not
replace either check.

## Completion

Revise the mathematical spec first, then C annotations. Run both exact commands and annotation-checking, repair recoverable failures in the same agent turn, and write `qcp-agent-report/v3` plus concise notes to this attempt directory. Do not claim controller acceptance.
"""


def _annotation_summary_errors(state: dict[str, Any], attempt: dict[str, Any]) -> list[str]:
    path = Path(str(attempt["input"]))
    if not path.is_file():
        return [f"annotation blocker summary is missing: {path}"]
    text = path.read_text(encoding="utf-8")
    errors: list[str] = []
    if MAIN_SUMMARY_MARKER in text:
        errors.append("main agent must replace every MAIN_AGENT template comment")
    for heading in ANNOTATION_SUMMARY_HEADINGS:
        match = re.search(
            rf"^## {re.escape(heading)}\s*$\n(.*?)(?=^## |\Z)",
            text,
            flags=re.MULTILINE | re.DOTALL,
        )
        if match is None:
            errors.append(f"required main-agent summary section is missing: {heading}")
            continue
        body = re.sub(r"<!--.*?-->", "", match.group(1), flags=re.DOTALL).strip()
        if len(body) < 20:
            errors.append(f"main-agent summary section is empty or too vague: {heading}")
    required_fragments = [
        str(attempt["attempt_id"]),
        str(attempt["source_version"]),
        str(attempt["report"]),
        str(attempt["output"]),
        str(state["main_root"]),
        str(attempt.get("retry_reason") or ""),
        ".agents/skills/annotation-filling/SKILL.md",
        ".agents/skills/annotation-checking/SKILL.md",
        _controller_command(state, "symexec", "--round", str(attempt["round"])),
        _controller_command(
            state,
            "coq-check",
            "--round",
            str(attempt["round"]),
            "--target-kind",
            "formal-case-lib",
        ),
    ]
    required_fragments.extend(
        str(state["target_files"][key])
        for key in (
            "c_file",
            "formal_case_lib",
            "proof_manual_file",
            "goal_file",
            "proof_auto_file",
            "goal_check_file",
            "proof_diagnostics_file",
            "diagnostics_snapshot",
        )
    )
    for item in attempt.get("feedback_sources", []):
        required_fragments.extend(
            [str(item["phase"]), str(item["attempt_id"]), str(item["markdown"]), str(item["json"])]
        )
    for fragment in required_fragments:
        if fragment not in text:
            errors.append(f"controller-owned summary content was removed: {fragment}")
    if int(attempt.get("annotation_iteration", 0)) >= 3 and "third or later annotation iteration" not in text:
        errors.append("repeated annotation retry must preserve the broader-redesign instruction")
    return errors


def _render_agent_input(
    state: dict[str, Any],
    *,
    phase: str,
    round_id: str,
    attempt_id: str,
    paths: dict[str, Path],
    source_version: str,
    allowed_write_paths: list[str],
    previous_attempts: list[dict[str, Any]],
    required_lessons: list[dict[str, Any]],
    attempt_index: int,
    annotation_iteration: int = 0,
    feedback_sources: list[dict[str, str]] | None = None,
    retry_reason: str | None = None,
) -> str:
    if phase == "annotation" and annotation_iteration > 1:
        return _render_annotation_block_summary_template(
            state,
            round_id=round_id,
            attempt_id=attempt_id,
            paths=paths,
            source_version=source_version,
            allowed_write_paths=allowed_write_paths,
            previous_attempts=previous_attempts,
            required_lessons=required_lessons,
            annotation_iteration=annotation_iteration,
            feedback_sources=feedback_sources or [],
            retry_reason=str(retry_reason or "annotation-feedback"),
        )
    target = state["target_files"]
    rules = _format_list(_rules_source(phase))
    previous = _format_list(
        [
            " | ".join(
                str(item.get(key))
                for key in ("attempt_id", "report", "output", "annotation_history_directory")
                if item.get(key)
            )
            for item in previous_attempts
        ]
    )
    lessons = "\n".join(f"- {item.get('must_address', item)}" for item in required_lessons) or "- none"
    common = f"""# {phase} handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `{round_id}`
- Attempt: `{attempt_id}` (index {attempt_index})
- Main root: `{state['main_root']}`
- `source_version`: `{source_version}`
- Terminal report: `{paths['report']}`
- Optional human notes: `{paths['output']}`

## Target files

- C: `{target['c_file']}`
- `formal_case_lib`: `{target['formal_case_lib']}`
- Manual: `{target['proof_manual_file']}`
- Goal/auto/check: `{target['goal_file']}`, `{target['proof_auto_file']}`, `{target['goal_check_file']}`
- Diagnostics: `{target['proof_diagnostics_file']}`, `{target['diagnostics_snapshot']}`

## Rules to read

{rules}

## Previous attempts

{previous}

Required lessons:

{lessons}
"""
    if phase == "annotation":
        symexec = _controller_command(state, "symexec", "--round", round_id)
        coq = _controller_command(state, "coq-check", "--round", round_id, "--target-kind", "formal-case-lib")
        checking_start = _controller_command(
            state, "timing-stage", "--round", round_id, "--stage", "annotation-checking", "--event", "start"
        )
        checking_finish = _controller_command(
            state, "timing-stage", "--round", round_id, "--stage", "annotation-checking", "--event", "finish"
        )
        feedback = feedback_sources or []
        feedback_text = (
            "\n".join(
                f"- `{item['phase']}` `{item['attempt_id']}`: Markdown `{item['markdown']}`; JSON `{item['json']}`"
                for item in feedback
            )
            if feedback
            else "- none (initial annotation iteration)"
        )
        iteration_rules = (
            "This is the initial iteration. Read both annotation skill files completely, follow their linked guides, "
            "and inspect the correct/incorrect examples relevant to this case before editing."
            if annotation_iteration == 1
            else "This is a continuation of the same annotation-agent session. Before editing, reload both annotation "
            "skill files completely and read every listed Markdown and JSON blocker source; do not rely on a summary."
        )
        broader = (
            "\nThis is the third or later annotation iteration. Reassess the design at a larger scale: consider "
            "refactoring the mathematical specification, function contracts, loop invariants, assertions, and call "
            "instantiations together rather than accumulating local patches.\n"
            if annotation_iteration >= 3
            else ""
        )
        current_session = state.get("annotation_session")
        annotation_session_id = (
            str(current_session["session_id"])
            if isinstance(current_session, dict)
            else f"{state['case']}-annotation-agent"
        )
        return common + f"""

## Persistent annotation agent

- Session: `{annotation_session_id}`
- Iteration: {annotation_iteration}

{iteration_rules}

Feedback appended for this iteration:

{feedback_text}
{broader}

## Problem context

{_problem_context_text(state.get('problem_context', {}))}

## Writable formal paths

{_format_list(allowed_write_paths)}

Generated files may change only through the exact symbolic-execution command below.

## Commands

```text
{symexec}
{coq}
{checking_start}
{checking_finish}
```

Run the timing-stage start command immediately before invoking annotation-checking, and run the finish command only
after its review/repair loop completes. These commands measure the whole annotation-checking stage; they do not
replace either check.

## Completion

Design the mathematical spec first, edit `formal_case_lib`, then C annotations, run both commands, and run annotation-checking. Repair recoverable failures in this agent turn. Write `qcp-agent-report/v3` with terminal `status`, exact `changed_files`, the three check statuses, and concrete `blockers` only when needed. Do not claim controller acceptance.
"""

    goal = state.get("source_goal_version") or {}
    witnesses = [str(item) for item in goal.get("target_witnesses", [])]
    return common + f"""

## VC checking inputs

- `source_goal_version`: `{goal.get('digest', '')}`
- Group plan output: `{paths['group_plan']}`
- Maximum witnesses per group: {state['max_witnesses_per_group']}

Target witnesses:

{_format_list(witnesses)}

All formal files are read-only. Put detailed natural-language witness analysis in `{paths['output']}` for humans and future retries. Keep `group_plan.json` machine-minimal: schema, version, and groups with `id`, `witnesses`, `depends_on`, plus short optional `strategy`/`helpers`. Write `qcp-agent-report/v3` with terminal `status`, the current version, and concrete `blockers` only when needed. Do not claim controller acceptance.
"""


def _next_round_id(state: dict[str, Any], phase: str) -> str:
    prefix = f"{state['case']}-{phase}-r"
    used = [int(key.rsplit("r", 1)[-1]) for key in state["rounds"] if key.startswith(prefix) and key.rsplit("r", 1)[-1].isdigit()]
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
) -> dict[str, Any]:
    report_root = Path(str(state["report_root"]))
    round_id = _next_round_id(state, phase)
    attempt_id = f"{round_id}-attempt-{attempt_index}"
    if phase == "annotation":
        session = state.get("annotation_session")
        annotation_iteration = int(session.get("iteration_count", 0)) + 1 if isinstance(session, dict) else 1
        paths = _annotation_paths(Path(str(state["run_root"])), annotation_iteration)
    else:
        paths = _round_paths(report_root, round_id)
        annotation_iteration = 0
    source = _source_version_for_state(state, annotated=phase != "annotation")
    target = state["target_files"]
    allowed = (
        [target["c_file"], target["formal_case_lib"], *[target[key] for key in GENERATED_KEYS]]
        if phase == "annotation"
        else []
    )
    write_text(
        paths["input"],
        _render_agent_input(
            state,
            phase=phase,
            round_id=round_id,
            attempt_id=attempt_id,
            paths=paths,
            source_version=str(source["digest"]),
            allowed_write_paths=allowed,
            previous_attempts=previous_attempts or [],
            required_lessons=required_lessons or [],
            attempt_index=attempt_index,
            annotation_iteration=annotation_iteration,
            feedback_sources=feedback_sources or [],
            retry_reason=retry_reason,
        ),
    )
    goal_digest = str((state.get("source_goal_version") or {}).get("digest") or "") or None
    write_json(paths["report"], _agent_report_payload(phase, goal_digest))
    write_text(paths["output"], "# Agent notes\n\nOptional concise analysis for humans and declared retries.")
    attempt: dict[str, Any] = {
        "attempt_id": attempt_id,
        "round": round_id,
        "phase": phase,
        "status": "awaiting-main-summary" if phase == "annotation" and annotation_iteration > 1 else "prepared",
        "report_directory": str(paths["directory"]),
        "input": str(paths["input"]),
        "report": str(paths["report"]),
        "output": str(paths["output"]),
        "source_version": str(source["digest"]),
        "source_goal_version": goal_digest,
        "allowed_write_paths": allowed,
        "compact_attempt_index": attempt_index,
        "created_at": _utc(),
    }
    if phase == "annotation":
        _ensure_formal_case_lib_seed(state)
        history = annotation_history_root(Path(str(state["run_root"]))) / attempt_id
        attempt["annotation_history_directory"] = str(history)
        attempt["annotation_iteration"] = annotation_iteration
        attempt["feedback_sources"] = feedback_sources or []
        attempt["retry_reason"] = retry_reason
        _archive_annotation_stage(state, attempt, "before")
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
        if annotation_iteration == 1:
            attempt["input_sha256"] = _file_digest(paths["input"])
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
                    "consider_broader_refactor": False,
                }
            ]
        else:
            state["next_actions"] = [
                {
                    "id": f"summarize-{attempt_id}",
                    "kind": "main-owned-action",
                    "action": "annotation-summary-ready",
                    "phase": phase,
                    "attempt_id": attempt_id,
                    "input": str(paths["input"]),
                    "feedback_sources": feedback_sources or [],
                    "consider_broader_refactor": annotation_iteration >= 3,
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
    round_id = _next_round_id(state, "vc-proving")
    run_root = Path(str(state["run_root"]))
    report_directory = round_report_root(run_root, round_id)
    directory = run_root / round_id
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
        "source_goal_version": str(state["source_goal_version"]["digest"]),
        "max_parallel_group_workers": DEFAULT_MAX_PARALLEL_GROUP_WORKERS,
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
    candidates = [item for item in state["attempts"].values() if item.get("phase") == phase and item.get("status") not in {"stale", "superseded"}]
    return candidates[-1] if candidates else None


def _sync_group_actions(state: dict[str, Any], attempt: dict[str, Any]) -> None:
    if attempt.get("status") != "groups-ready":
        state["next_actions"] = []
        return
    manifest = _json_load(Path(str(attempt["group_workers_manifest"])), {})
    groups = manifest.get("groups") if isinstance(manifest, dict) and isinstance(manifest.get("groups"), list) else []
    accepted = set(state.get("accepted_groups", {}).get(attempt["round"], []))
    if groups and len(accepted) == len(groups):
        state["next_actions"] = [
            {
                "id": f"vc-proving-verify-{attempt['round']}",
                "kind": "main-owned-action",
                "action": "vc-proving-verify",
                "round": attempt["round"],
                "attempt_id": attempt["attempt_id"],
            }
        ]
        return
    actions: list[dict[str, Any]] = []
    running = sum(1 for item in attempt["groups"].values() if item.get("status") == "running")
    available = max(0, int(attempt["max_parallel_group_workers"]) - running)
    by_id = {str(group["id"]): group for group in groups}
    for group_id in manifest.get("order", []):
        if available <= 0:
            break
        group = by_id.get(str(group_id))
        if not group or str(group_id) in accepted:
            continue
        status = attempt["groups"].get(str(group_id), {}).get("status")
        if status in {"running", "returned", "completed", "blocked", "stale"}:
            continue
        if not all(str(dep) in accepted for dep in group.get("depends_on", [])):
            continue
        attempt["groups"].setdefault(str(group_id), {"status": "prepared", "attempt_index": 1})
        report_dir = Path(str(group["report_directory"]))
        actions.append(
            {
                "id": f"spawn-{attempt['round']}-{group_id}",
                "kind": "spawn-group-worker",
                "phase": VC_PROVING_PHASE,
                "attempt_id": f"{attempt['round']}:{group_id}",
                "round": attempt["round"],
                "group_id": str(group_id),
                "input": str(report_dir / "group_worker_input.md"),
                "report": str(report_dir / "group_worker_report.json"),
            }
        )
        available -= 1
    state["next_actions"] = actions


def annotation_summary_ready(args: argparse.Namespace) -> int:
    """Validate and seal the main-written blocker summary before agent append."""

    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = state.get("attempts", {}).get(args.attempt)
    if not isinstance(attempt, dict) or attempt.get("phase") != "annotation":
        raise SystemExit(f"annotation attempt not found: {args.attempt}")
    session = state.get("annotation_session")
    if not isinstance(session, dict) or session.get("current_attempt") != args.attempt:
        raise SystemExit("annotation summary does not belong to the current persistent session attempt")
    if attempt.get("status") != "awaiting-main-summary":
        raise SystemExit(f"annotation attempt is not awaiting a main-agent summary: {attempt.get('status')}")
    errors = _annotation_summary_errors(state, attempt)
    if errors:
        print(json.dumps({"status": "invalid", "errors": errors}, indent=2))
        return 1
    attempt["input_sha256"] = _file_digest(Path(str(attempt["input"])))
    attempt["status"] = "prepared"
    session["status"] = "prepared"
    state["next_actions"] = [
        {
            "id": f"append-{attempt['attempt_id']}",
            "kind": "append-annotation-agent",
            "phase": "annotation",
            "session_id": session["session_id"],
            "attempt_id": attempt["attempt_id"],
            "input": attempt["input"],
            "report": attempt["report"],
            "feedback_sources": attempt.get("feedback_sources", []),
            "consider_broader_refactor": int(attempt.get("annotation_iteration", 0)) >= 3,
        }
    ]
    _append_event(
        run_root,
        state,
        "annotation-summary-ready",
        attempt=attempt["attempt_id"],
        input_sha256=attempt["input_sha256"],
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "prepared",
                "attempt": attempt["attempt_id"],
                "next_action": state["next_actions"][0]["id"],
            },
            indent=2,
        )
    )
    return 0


def step(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    phase = state["phase"]
    if phase == "intake":
        state["phase"] = "annotation"
        _init_round_attempt(state, phase="annotation")
    elif phase == "annotation":
        if "annotation" in state["accepted_rounds"]:
            state["phase"] = "vc-checking"
            _init_round_attempt(state, phase="vc-checking")
        elif _current_attempt(state, "annotation") is None:
            _init_round_attempt(state, phase="annotation")
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
            state["next_actions"] = [
                {
                    "id": f"vc-proving-verify-{attempt['round']}",
                    "kind": "main-owned-action",
                    "action": "vc-proving-verify",
                    "round": attempt["round"],
                    "attempt_id": attempt["attempt_id"],
                }
            ]
        elif attempt["status"] == "verified":
            state["phase"] = "final-candidate-apply"
            state["next_actions"] = [{"id": "final-candidate-apply", "kind": "main-owned-action", "action": "final-apply"}]
    elif phase == "final-candidate-apply":
        state["next_actions"] = [{"id": "final-candidate-apply", "kind": "main-owned-action", "action": "final-apply"}]
    elif phase == "final-check":
        final_apply_status = state.get("final_apply", {}).get("status")
        if final_apply_status == "passed":
            state["next_actions"] = [{"id": "final-check", "kind": "main-owned-action", "action": "final-check"}]
        elif final_apply_status == "rolled-back":
            state["phase"] = "final-candidate-apply"
            state["next_actions"] = [
                {"id": "final-candidate-apply", "kind": "main-owned-action", "action": "final-apply"}
            ]
        else:
            state["next_actions"] = []
    elif phase == "done":
        state["next_actions"] = []
    _append_event(run_root, state, "controller-step", actions=[item["id"] for item in state["next_actions"]])
    _save_state(run_root, state)
    print(json.dumps({"phase": state["phase"], "next_actions": state["next_actions"]}, indent=2))
    return 0


def spawn_instructions(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    state = _load_state(_run_root_from_id(main_root, args.run))
    action = next((item for item in state["next_actions"] if item.get("id") == args.next_action), None)
    if action is None or action.get("kind") not in {
        "spawn-attempt",
        "spawn-group-worker",
        "spawn-annotation-agent",
        "append-annotation-agent",
    }:
        raise SystemExit(f"spawn action not found: {args.next_action}")
    if action["kind"] in {"spawn-annotation-agent", "append-annotation-agent"}:
        attempt = state.get("attempts", {}).get(str(action.get("attempt_id")))
        if not isinstance(attempt, dict) or attempt.get("status") != "prepared":
            raise SystemExit("annotation attempt is not prepared for delivery")
        input_path = Path(str(attempt["input"]))
        if not input_path.is_file() or _file_digest(input_path) != attempt.get("input_sha256"):
            raise SystemExit("annotation agent_input.md changed after controller validation")
    if action["kind"] == "spawn-group-worker":
        from path_utils import group_worker_spawn_message

        message = group_worker_spawn_message(action["input"], action["report"])
    elif action["kind"] == "spawn-annotation-agent":
        message = _annotation_spawn_message(action)
    elif action["kind"] == "append-annotation-agent":
        message = _annotation_append_message(action)
    else:
        message = _spawn_message(Path(str(action["input"])), Path(str(action["report"])))
    print(message)
    return 0
