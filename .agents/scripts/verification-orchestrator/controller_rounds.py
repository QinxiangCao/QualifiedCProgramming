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

from controller_invocations import (
    hydrate_actions,
    hydrate_waiting_deliveries,
)
from controller_state import (
    GENERATED_KEYS,
    _append_event,
    _archive_annotation_stage,
    _current_version_errors,
    _file_digest,
    _formal_case_lib_is_active,
    _generated_artifact_module_spellings_for_state,
    _json_load,
    _load_state,
    _run_root_from_id,
    _save_state,
    _source_version_for_state,
    _utc,
    _validated_annotation_attempt_paths,
    _validated_proving_attempt_paths,
    _verified_reuse_source_build,
)
from controller_dune import _preparation_action
from coq_tooling import dune_preparation_receipt_errors
from path_utils import (
    annotation_attempt_directory_name,
    annotation_attempt_report_root,
    annotation_history_root,
    fixed_path_under,
    reuse_source_build_workspace,
    round_report_root,
    vc_checking_debug_script,
    write_json,
    write_text,
)
from prepare_group_workers import resolve_group_workers_manifest
from proof_manual_utils import (
    lemma_by_name,
    lemma_target_symbol,
    parse_manual_file,
)
from symexec_tooling import _lexical_regular_file_snapshot, _snapshot_text
from verify_group_results import validate_group_for_acceptance_result

DEFAULT_MAX_PARALLEL_GROUP_WORKERS = 5
VC_PROVING_PHASE = "vc-proving-preparing"
ANNOTATION_GAP_FAILURE_CLASS = "annotation-gap"
# A delivery carries formal sources and owner narrative. Feedback cites the
# narrative; report-only repair preserves the formal bytes.
FORMAL_ARTIFACT_ROLES = ("proof_manual", "group_worker_lib")
NOTES_ARTIFACT_ROLE = "output"
GROUP_NOTES_FILENAME = "group_worker_output.md"
ANNOTATION_CAUSAL_FAILURE_CLASSES = frozenset(
    {ANNOTATION_GAP_FAILURE_CLASS, "specification-gap", "dependency-gap"}
)
VC_CHECKING_BLOCKER_RETRY_PHASES = {
    ANNOTATION_GAP_FAILURE_CLASS: "annotation",
    "specification-gap": "annotation",
    "dependency-gap": "annotation",
    "source-version": "annotation",
    "plan-defect": "vc-checking",
    "report-defect": "vc-checking",
    "infrastructure": "vc-checking",
}
MAIN_SUMMARY_MARKER = "<!-- MAIN_AGENT:"
ANNOTATION_SUMMARY_HEADINGS = (
    "Main-agent blocker conclusion",
    "Evidence and causal analysis",
    "Reflection on the previous annotation attempt",
    "Required annotation repair",
    "Scope decision",
)


def _consider_broader_refactor(attempt: dict[str, Any]) -> bool:
    """Require redesign review only after two consecutive annotation causes."""

    count = attempt.get("annotation_causal_retry_count", 0)
    return isinstance(count, int) and not isinstance(count, bool) and count >= 2


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
        "reuse_hints": directory / "reuse_hints",
    }


def _annotation_paths(run_root: Path, annotation_iteration: int) -> dict[str, Path]:
    directory = annotation_attempt_report_root(run_root, annotation_iteration)
    return {
        "directory": directory,
        "input": directory / "agent_input.md",
        "report": directory / "agent_report.json",
        "output": directory / "agent_output.md",
        "group_plan": directory / "group_plan.json",
        "reuse_hints": directory / "reuse_hints",
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
        for path in item.get("evidence", [])
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
        "Revise the current main-root formal C annotation and edit the case lib "
        "only when the handoff marks that existing path writable, "
        f"use the controller checks as needed for feedback, complete the semantic review, "
        f"and write the terminal result to {action['report']}."
        + broader
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
                ".agents/skills/annotation-filling/SKILL.md",
                ".agents/skills/annotation-filling/workflows/annotation-filling.md",
                ".agents/skills/annotation-checking/SKILL.md",
                ".agents/skills/annotation-checking/workflows/annotation-checking.md",
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


def _fully_qualified_debug_targets(
    state: dict[str, Any],
    manual_path: Path,
    names: list[str],
    *,
    manual_text: str | None = None,
) -> dict[str, str]:
    try:
        _prelude, manual_lemmas = parse_manual_file(
            manual_text
            if manual_text is not None
            else manual_path.read_text(encoding="utf-8")
        )
    except (OSError, ValueError) as exc:
        raise SystemExit(
            f"cannot render fully-qualified VC debug targets from {manual_path}: {exc}"
        ) from exc
    manual_by_name = lemma_by_name(manual_lemmas)
    target = state["target_files"]
    result: dict[str, str] = {}
    for name in names:
        lemma = manual_by_name.get(name)
        symbol = lemma_target_symbol(lemma) if lemma is not None else None
        if symbol is None:
            raise SystemExit(
                f"generated manual goal has no simple fully-qualified debug target: {name}"
            )
        result[name] = (
            f"{target['active_case_theory']}.{target['case_name']}_goal.{symbol}"
        )
    return result


def _sealed_group_digest(
    attempt: dict[str, Any], group: dict[str, Any], artifact: str
) -> str:
    """Return the controller-recorded digest for one reusable group artifact."""

    group_id = str(group.get("id") or "")
    reuse_record = attempt.get("reuse_group_artifacts")
    reuse_groups = (
        reuse_record.get("groups") if isinstance(reuse_record, dict) else None
    )
    if isinstance(reuse_groups, dict):
        group_record = reuse_groups.get(group_id)
        if isinstance(group_record, dict) and group_record.get(artifact):
            return str(group_record[artifact])
    accepted = (
        attempt.get("groups", {}).get(group_id, {}).get("accepted_artifact_sha256")
    )
    if isinstance(accepted, dict) and accepted.get(artifact):
        return str(accepted[artifact])
    raise ValueError(
        f"proof reuse source `{group_id}` has no sealed {artifact} digest"
    )


def _latest_reusable_vc_proving_round(state: dict[str, Any]) -> str | None:
    """Return the immediately preceding sealed proving source eligible for hints."""

    proving_attempts = [
        item
        for item in state.get("attempts", {}).values()
        if item.get("phase") == VC_PROVING_PHASE
    ]
    if not proving_attempts:
        return None
    attempt = proving_attempts[-1]
    try:
        attempt_paths = _validated_proving_attempt_paths(state, attempt)
    except (OSError, ValueError):
        return None
    manifest_path = attempt_paths["group_workers_manifest"]
    base_path = attempt_paths["base_manifest"]
    if (
        not manifest_path.is_file()
        or not base_path.is_file()
        or _file_digest(manifest_path)
        != str(attempt.get("group_workers_manifest_sha256") or "")
        or _file_digest(base_path) != str(attempt.get("base_manifest_sha256") or "")
    ):
        return None
    try:
        reuse_seed_root = _validated_reuse_raw_root(state, attempt)
        manifest = resolve_group_workers_manifest(
            manifest_path,
            main_root=Path(str(state["main_root"])),
            seed_root=reuse_seed_root,
            expected_run_root=Path(str(state["run_root"])),
            expected_round=str(attempt["round"]),
        )
    except (OSError, TypeError, ValueError, SystemExit):
        return None
    groups = (
        manifest.get("groups")
        if isinstance(manifest, dict) and isinstance(manifest.get("groups"), list)
        else []
    )
    if not groups or any(
        isinstance(group_state, dict)
        and group_state.get("status") in {"running", "returned", "repair-prepared"}
        for group_state in attempt.get("groups", {}).values()
    ):
        return None
    if not (
        _reuse_group_artifacts_are_sealed(attempt, groups)
        or _accepted_group_artifacts_are_sealed(attempt, groups)
    ):
        return None
    snapshot = attempt.get("reuse_source_snapshot")
    if not isinstance(snapshot, dict):
        return None
    if not isinstance(state.get("main_root"), str) or not isinstance(
        state.get("target_files", {}).get("proof_auto_file"), str
    ):
        return None
    try:
        _verified_reuse_source_build(
            main_root=Path(str(state["main_root"])),
            run_root=Path(str(state["run_root"])),
            round_id=str(attempt["round"]),
            sealed=snapshot,
            source_goal_version=str(attempt.get("source_goal_version") or ""),
        )
    except (OSError, ValueError):
        return None
    try:
        _sealed_reuse_raw_artifacts(state, attempt)
    except (OSError, TypeError, ValueError):
        return None
    try:
        _sealed_public_helper_snapshot(state, attempt, manifest)
    except (OSError, TypeError, UnicodeError, ValueError):
        return None
    if attempt.get("failure_status") == "parent-verify-failed":
        result_path = Path(str(attempt.get("proving_merged_result") or ""))
        expected_result = str(attempt.get("failed_result_sha256") or "")
        if (
            attempt.get("failure_source_goal_version")
            == attempt.get("source_goal_version")
            and result_path.is_file()
            and expected_result
            and _file_digest(result_path) == expected_result
        ):
            return str(attempt["round"])
        return None
    # A structurally invalid report is not a trustworthy provenance source;
    # binding the next vc-checking round to it would create a retry dead end.
    failure_statuses = {"blocked", "compact-error-retry-exhausted"}
    if any(
        isinstance(group, dict) and group.get("status") in failure_statuses
        for group in attempt.get("groups", {}).values()
    ):
        record = attempt.get("reuse_group_artifacts")
        valid_groups = (
            record.get("structurally_valid_groups")
            if isinstance(record, dict)
            else None
        )
        if not isinstance(valid_groups, list) or not valid_groups:
            return None
        return str(attempt["round"])
    if (
        attempt.get("status") == "stale"
        and attempt.get("proof_reuse_eligible") is True
        and attempt.get("stale_from_status") == "verified"
    ):
        result_path = Path(str(attempt.get("proving_merged_result") or ""))
        expected_result = str(attempt.get("verified_result_sha256") or "")
        result = _json_load(result_path, {})
        if (
            result_path.is_file()
            and expected_result
            and _file_digest(result_path) == expected_result
            and isinstance(result, dict)
            and result.get("status") == "passed"
            and result.get("source_goal_version") == attempt.get("source_goal_version")
        ):
            return str(attempt["round"])
    return None


def _validated_reuse_raw_root(
    state: dict[str, Any],
    attempt: dict[str, Any],
) -> Path:
    """Return the controller-owned lexical root for a sealed reuse snapshot."""

    raw_source = attempt.get("reuse_source_raw")
    if not isinstance(raw_source, dict):
        raise TypeError("proof reuse source lacks a sealed raw formal snapshot")
    raw_root_value = raw_source.get("root")
    if not isinstance(raw_root_value, str) or not raw_root_value:
        raise ValueError("proof reuse raw formal snapshot root is invalid")
    round_id = attempt.get("round")
    if not isinstance(round_id, str) or not round_id:
        raise ValueError("proof reuse source round identity is invalid")

    run_root = Path(str(state["run_root"]))
    try:
        expected_root = fixed_path_under(
            run_root / round_id / "reuse_source_raw",
            run_root,
            label="proof reuse raw formal snapshot root",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc

    recorded_root = Path(raw_root_value).expanduser()
    normalized_root = Path(os.path.abspath(os.fspath(recorded_root)))
    if (
        not recorded_root.is_absolute()
        or recorded_root != normalized_root
        or normalized_root != expected_root
    ):
        raise ValueError(
            "proof reuse raw formal snapshot root differs from its fixed round topology"
        )
    try:
        fixed_root = fixed_path_under(
            normalized_root,
            run_root,
            label="proof reuse raw formal snapshot root",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    if not fixed_root.is_dir():
        raise ValueError("proof reuse raw formal snapshot root is not a directory")
    return fixed_root


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


def _sealed_public_helper_snapshot(
    state: dict[str, Any],
    attempt: dict[str, Any],
    manifest: dict[str, Any],
) -> dict[str, Any]:
    """Read the exact round-local public-helper snapshot and verify its seal."""

    round_id = str(attempt.get("round") or "")
    if not round_id:
        raise ValueError("proof reuse source round identity is missing")
    owner = Path(str(state["run_root"])) / round_id
    expected_path = owner / "public_helper_snapshot.txt"
    raw_path = manifest.get("public_helper_lemma_lib")
    if not isinstance(raw_path, str) or Path(raw_path) != expected_path:
        raise ValueError(
            "proof reuse public helper snapshot differs from its fixed round path"
        )
    snapshot = _stable_fixed_file_snapshot(
        expected_path,
        owner=owner,
        label="proof reuse public helper snapshot",
    )
    expected_sha256 = manifest.get("public_helper_lemma_lib_sha256")
    if snapshot.get("sha256") != expected_sha256:
        raise ValueError("sealed public helper snapshot changed")
    return snapshot


def _sealed_reuse_raw_artifacts(
    state: dict[str, Any],
    attempt: dict[str, Any],
) -> dict[str, dict[str, Any]]:
    """Validate nullable raw reuse artifacts against the sealed base topology."""

    raw_source = attempt.get("reuse_source_raw")
    if not isinstance(raw_source, dict):
        raise TypeError("proof reuse source lacks a sealed raw formal snapshot")
    raw_root = _validated_reuse_raw_root(state, attempt)
    raw_files = raw_source.get("files")
    expected_keys = {"goal_file", "proof_manual_file", "formal_case_lib"}
    if not isinstance(raw_files, dict) or set(raw_files) != expected_keys:
        raise ValueError("proof reuse raw formal snapshot record is invalid")

    base_path = Path(str(attempt.get("base_manifest") or ""))
    base = _json_load(base_path, {})
    seed = base.get("seed_sha256") if isinstance(base, dict) else None
    if (
        not isinstance(seed, dict)
        or set(seed) != {"proof_manual", "formal_case_lib"}
        or base.get("proof_manual") != state["target_files"]["proof_manual_file"]
        or base.get("formal_case_lib") != state["target_files"]["formal_case_lib"]
    ):
        raise ValueError("proof reuse base manifest topology is invalid")
    expected_optional = {
        "proof_manual_file": seed.get("proof_manual"),
        "formal_case_lib": seed.get("formal_case_lib"),
    }
    records: dict[str, dict[str, Any]] = {}
    for key in ("goal_file", "proof_manual_file", "formal_case_lib"):
        digest = raw_files.get(key)
        if key in expected_optional and digest != expected_optional[key]:
            raise ValueError(
                f"proof reuse raw formal snapshot topology differs from base: {key}"
            )
        if digest is not None and (
            not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        ):
            raise ValueError(f"proof reuse raw formal snapshot digest is invalid: {key}")
        if key == "goal_file" and digest is None:
            raise ValueError("proof reuse raw generated goal record is null")
        relative_value = state["target_files"].get(key)
        if not isinstance(relative_value, str) or not relative_value:
            raise ValueError(
                f"proof reuse raw formal artifact identity is invalid: {key}"
            )
        relative = Path(relative_value)
        if (
            relative.is_absolute()
            or ".." in relative.parts
            or os.fspath(relative) != relative_value
        ):
            raise ValueError(
                f"proof reuse raw formal artifact identity is not canonical: {key}"
            )
        try:
            path = fixed_path_under(
                raw_root / relative,
                raw_root,
                label=f"proof reuse raw formal artifact {key}",
            )
        except SystemExit as exc:
            raise ValueError(str(exc)) from exc
        if digest is None:
            if os.path.lexists(path):
                raise ValueError(
                    f"absent proof reuse raw formal artifact appeared: {key}"
                )
        else:
            snapshot = _stable_fixed_file_snapshot(
                path,
                owner=raw_root,
                label=f"proof reuse raw formal artifact {key}",
            )
            if snapshot.get("sha256") != digest:
                raise ValueError(f"proof reuse raw formal snapshot changed: {key}")
        records[key] = {
            "path": path,
            "sha256": digest,
            **(
                {"data": snapshot["data"]}
                if digest is not None
                else {}
            ),
        }
    return records


def _proof_reuse_handoff(
    state: dict[str, Any],
    *,
    round_id: str,
    paths: dict[str, Path],
    previous_round: str | None,
) -> str:
    current_debug = _controller_command(state, "coq-debug", "--round", round_id)
    current_script = vc_checking_debug_script(
        Path(str(state["run_root"])),
        round_id,
    )
    current = f"""## Proof-state inspection

- Current debug script: `{current_script}`
- Current debug command: `{current_debug}`

The `.coq_debug` directory may contain only that declared script. Before a goal block, the script may contain only
imports, scope openings, and `Set Printing All.`. Inspect every listed target with this exact command shape:

```coq
Goal <fully-qualified-target>.
Show.
(* optional proof tactics and additional Show. commands *)
Abort.
```

The fully-qualified target must be copied from the current targets in `VC checking inputs` or, for the preserved
previous build, from the `Previous comparison target` list below. The first executable command after `Goal` must be
`Show.` so it binds the original generated goal. Definitions, declarations, `Load`, command wrappers, and attributes
are forbidden. Run the exact controller command after writing the final script. Current and preserved debug use the
same controller-owned load-path plan: only current-case closure files live in the sealed build, while fixed dependency
`.vo` files are read from the selected sealed base (Dune `_build/default` or Makefile main-root artifacts) and are not
copied into the local build tree. Their accepted snapshot digest is bound into the combined build seal; those files do
not increase the local build file count.
"""
    if previous_round is None:
        return (
            current
            + """

## Proof reuse

There is no immediately preceding sealed vc-proving source eligible for comparison. Skip proof-reuse comparison and do not create reuse-hint files.
"""
        )
    previous = state.get("attempts", {}).get(previous_round, {})
    try:
        previous_paths = _validated_proving_attempt_paths(state, previous)
    except (OSError, ValueError) as exc:
        raise SystemExit(f"proof reuse source path topology is invalid: {exc}") from exc
    manifest_path = previous_paths["group_workers_manifest"]
    try:
        reuse_seed_root = _validated_reuse_raw_root(state, previous)
    except (OSError, TypeError, ValueError) as exc:
        raise SystemExit(f"proof reuse source seed is invalid: {exc}") from exc
    manifest = resolve_group_workers_manifest(
        manifest_path,
        main_root=Path(str(state["main_root"])),
        seed_root=reuse_seed_root,
        expected_run_root=Path(str(state["run_root"])),
        expected_round=str(previous["round"]),
    )
    reference_script = (
        reuse_source_build_workspace(Path(str(state["run_root"])), previous_round)
        / ".coq_debug"
        / "reuse-source.v"
    )
    reference_debug = _controller_command(state, "coq-debug", "--round", previous_round)
    groups: list[str] = []
    try:
        _sealed_public_helper_snapshot(state, previous, manifest)
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        raise SystemExit(
            f"proof reuse public helper candidate pool is invalid: {exc}"
        ) from exc
    reusable_group_ids = _reusable_group_ids(previous, manifest)
    for group in manifest.get("groups", []) if isinstance(manifest, dict) else []:
        if not isinstance(group, dict):
            continue
        if str(group.get("id") or "") not in reusable_group_ids:
            continue
        witnesses = [
            item for item in group.get("witnesses", []) if isinstance(item, dict)
        ]
        routes = ", ".join(
            f"{item.get('name')}={item.get('proof_mode')}" for item in witnesses
        )
        report_directory = Path(str(group.get("report_directory") or ""))
        group_directory = Path(str(group.get("directory") or ""))
        manual_path = Path(str(group.get("proof_manual") or ""))
        comparison_names: list[str] = []
        for witness in witnesses:
            mode = str(witness.get("proof_mode") or "")
            if mode == "aggressive_pre_process":
                comparison_names.extend(
                    str(split.get("name") or "")
                    for split in witness.get("split_goals", [])
                    if isinstance(split, dict)
                )
            elif mode == "LLM_pre_process":
                comparison_names.append(str(witness.get("name") or ""))
            else:
                raise SystemExit(
                    f"previous proof reuse manifest has an invalid proof mode: {mode}"
                )
        if not comparison_names or any(not name for name in comparison_names):
            raise SystemExit(
                f"previous proof reuse group has no valid comparison targets: {group.get('id')}"
            )
        try:
            manual_snapshot = _stable_fixed_file_snapshot(
                manual_path,
                owner=group_directory,
                label="proof reuse group manual",
            )
            if manual_snapshot.get("sha256") != _sealed_group_digest(
                previous, group, "proof_manual"
            ):
                raise ValueError("sealed proof reuse group manual changed")
            manual_text = _snapshot_text(
                manual_snapshot,
                label="proof reuse group manual",
            )
        except (OSError, UnicodeError, ValueError) as exc:
            raise SystemExit(str(exc)) from exc
        previous_targets = _fully_qualified_debug_targets(
            state,
            manual_path,
            comparison_names,
            manual_text=manual_text,
        )
        target_lines = "\n".join(
            f"  - Previous comparison target `{name}` -> `{previous_targets[name]}`"
            for name in comparison_names
        )
        raw_worker_lib = group.get("group_worker_lib")
        worker_lib = (
            Path(raw_worker_lib)
            if isinstance(raw_worker_lib, str) and raw_worker_lib
            else None
        )
        lib_summary = (
            f"group_worker_lib `{worker_lib}`"
            if worker_lib is not None
            else "no group_worker_lib in this group topology"
        )
        group_line = (
            f"- Group `{group.get('id')}` ({routes or 'no routes'}): copied manual `{manual_path}`; "
            f"{lib_summary}; notes `{report_directory / 'group_worker_output.md'}`; "
            f"report `{report_directory / 'group_worker_report.json'}`"
        )
        detail_text = target_lines
        groups.append(group_line + (f"\n{detail_text}" if detail_text else ""))
    group_text = "\n".join(groups) or "- no readable previous group entries"
    return (
        current
        + f"""

## Proof reuse

The immediately preceding vc-proving round `{previous_round}` is the controller-selected sealed comparison source
(either a failed proving round or a previously verified round made stale by an annotation/freshness retry). Compare
only against this round while writing the natural-language proof strategies after every current `proof_mode` is fixed.

- Previous manifest: `{manifest_path}`
- Previous goal debug script: `{reference_script}`
- Previous goal debug command: `{reference_debug}`
- Per-group reuse-hint directory to create: `{paths["reuse_hints"]}`

Previous group files and exact reference comparison targets:

{group_text}

Within every mixed-mode current group, order `group_plan.json` witnesses with all
`aggressive_pre_process` witnesses before all `LLM_pre_process` witnesses, preserving relative order within each
segment. This makes plan traversal identical to the required reuse category sequence. Then list all planned helpers
first, all aggressive split goals next, and only the `LLM_pre_process` top-level VCs last. Do not compare an
aggressive top-level VC. Every helper must be `from scratch`;
historical helper declarations are not comparison sources. For a split entailment `P |-- Q`,
proof `direct copy` additionally requires an exact current/previous semantic generated-goal fingerprint, including
the transitive local goal-definition closure and current formal-case spec while ignoring only the generated declaration
name. A changed fingerprint must be `partial proof-idea reuse` or `from scratch`. Partial reuse is an advisory design
hint: its Reason must explain the observed adapter/frame idea, but controller does not prove that natural-language claim. It is appropriate
not only for textually similar goals but also when the old proof can be
adapted through `P |-- P'` and `Q' |-- Q`, or by adding/cancelling a common spatial frame such as
`P ** R |-- Q ** R`. State the adapter/frame transformation in the Reason cell. Compare aggressive split goals
only against a previous aggressive route, and `LLM_pre_process` top-level goals only against a previous
`LLM_pre_process` route. A structurally valid but unaccepted failed group may supply partial
proof ideas only; it cannot supply direct proof/helper rows because its completed-looking blocks never passed controller group validation.

Create exactly one `{paths["reuse_hints"]}/<group-id>.md` for every proposed group. Use exactly these columns:
`Current goal | Decision | Previous file | Lines | Reason`, with `helper:<name>` rows for every planned local or public helper,
then one row per aggressive split goal, then one row per `LLM_pre_process` top-level VC. Decisions are exactly `direct copy`,
`partial proof-idea reuse`, or `from scratch`. Helper rows must use `from scratch` with `—` for both source fields;
proof rows cite an absolute copied manual. Every direct/partial range is a
positive `N` for a one-line declaration or `N-M` that exactly spans the compatible declaration from its first through last source line; an internal
subrange is invalid even when it contains every tactic. Direct copy additionally requires a complete source.
From-scratch rows use `—` for both file and lines. Debug scripts cover VC/split proof rows, not helper rows. The current
debug script must execute one `Show.` for every current proof row. When at least one proof row is direct/partial, the
reference script must execute `Show.` for every cited previous proof goal; when every proof row is from scratch, skip
the reference script and reference debug command entirely. After the final scripts and table agree, rerun the current
debug command and, when reference goals exist, the reference debug command so controller
records current receipts bound to the scripts, preserved builds, rounds, and versions. Missing receipts or later
script/build drift makes acceptance fail. You may inspect the listed lib/notes/report files for context, but table proof ranges point only to
the copied manual. These files are controller-transferred read-only hints,
not acceptance evidence.
"""
    )


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


def _main_summary_prompt(instruction: str) -> str:
    return f"{MAIN_SUMMARY_MARKER} {instruction} -->"


def _target_file_is_present(state: dict[str, Any], key: str) -> bool:
    return (
        Path(str(state["main_root"])) / str(state["target_files"][key])
    ).is_file()


def _optional_annotation_artifact_lines(
    state: dict[str, Any], *, annotation_owner: bool = True
) -> str:
    target = state["target_files"]
    formal_case_lib_active = _formal_case_lib_is_active(state)
    formal_case_lib_status = (
        (
            "present; edit it only when the case-specific spec needs a change"
            if annotation_owner
            else "present; read-only in this phase"
        )
        if formal_case_lib_active
        else (
            "missing in the run topology; there is no active/editable case lib, "
            "and this candidate path is read-only and must not be created"
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
    commands = [_controller_command(state, "symexec", "--round", round_id)]
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
    commands.extend(
        [
            _controller_command(
                state,
                "timing-stage",
                "--round",
                round_id,
                "--stage",
                "annotation-checking",
                "--event",
                event,
            )
            for event in ("start", "finish")
        ]
    )
    return "\n".join(commands), formal_case_lib_present


def _formal_case_lib_command_explanation(present: bool) -> str:
    if present:
        return (
            "The formal-case-lib Coq command uses the controller's single "
            "skinny-build plan: it stages only the exact current-case dependency "
            "closure, loads or builds its current prerequisites from the "
            "content-addressed cache, and reads fixed dependency `.vo` files from "
            "the selected sealed base. Before this local check, the controller asks "
            "the selected backend to prepare the exact case-lib target. A dependency "
            "that is merely unbuilt is therefore not an annotation defect."
        )
    return (
        "No formal-case-lib Coq command is listed because the optional candidate "
        "lib is absent from this run's fixed topology. The controller does not "
        "create a placeholder, and the annotation owner must not create a new lib "
        "at the read-only candidate path."
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


def _render_annotation_block_summary_template(
    state: dict[str, Any],
    *,
    round_id: str,
    attempt_id: str,
    paths: dict[str, Path],
    allowed_write_paths: list[str],
    previous_attempts: list[dict[str, Any]],
    required_lessons: list[dict[str, Any]],
    annotation_iteration: int,
    consider_broader_refactor: bool,
    feedback_sources: list[dict[str, str]],
    retry_reason: str,
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
    controller_evidence = (
        "\n".join(f"- {item.get('must_address', item)}" for item in required_lessons)
        or "- No additional controller evidence."
    )
    broader_rule = (
        "This repair follows at least two consecutive annotation-causal blockers. The scope decision must reassess "
        "the mathematical spec, function contracts, loop invariants, assertions, and call instantiations together "
        "and propose a broader redesign when the prior local design is the cause."
        if consider_broader_refactor
        else "Choose local repair or broader redesign from the evidence, and justify the boundary."
    )
    rules = _format_list(_rules_source("annotation"))
    commands, formal_case_lib_present = _annotation_commands(state, round_id)
    formal_case_lib_command_explanation = _formal_case_lib_command_explanation(
        formal_case_lib_present
    )
    return f"""# Annotation blocker summary and repair handoff

This is annotation iteration {annotation_iteration} in the run's single persistent annotation-agent session. The controller generated the factual sections and template; the main agent must read the original evidence and replace every `MAIN_AGENT` comment with a concrete summary before running `annotation-summary-ready`. Do not change controller-owned paths, evidence references, or commands.

## Assignment

- Session: `{session_id}`
- Round: `{round_id}`
- Attempt: `{attempt_id}`
- Retry reason: `{retry_reason}`
- Main root: `{state["main_root"]}`
- Terminal report: `{paths["report"]}`
- Human notes: `{paths["output"]}`

## Target files

- C: `{target["c_file"]}`
{_optional_annotation_artifact_lines(state)}
- Goal/auto/check: `{target["goal_file"]}`, `{target["proof_auto_file"]}`, `{target["goal_check_file"]}`

## Original blocker evidence

{source_lines}

Previous annotation attempt artifacts:

{prior_lines}

Controller-recorded blocker details:

{controller_evidence}

## Main-agent blocker conclusion

{_main_summary_prompt("State the primary failure, the blocked witness/check, and why this requires another annotation iteration. Distinguish annotation/spec defects from proof-only or tooling failures.")}

## Evidence and causal analysis

{_main_summary_prompt("Cite the decisive facts from the original Markdown/JSON or controller main-check evidence. Trace the failure to concrete specs, contracts, invariants, assertions, or call instantiations; separate symptoms from the root cause.")}

## Reflection on the previous annotation attempt

{_main_summary_prompt("Explain which earlier assumption or repair strategy was inadequate, what useful part should be preserved, and what the annotation agent must not repeat.")}

## Required annotation repair

{_main_summary_prompt("Give an actionable repair objective, affected formal locations, constraints that must remain true, and exact success criteria for symexec and annotation-checking; include formal_case_lib criteria only when the run topology contains that editable lib.")}

## Controller scope requirement

{broader_rule}

## Scope decision

{_main_summary_prompt("Choose the repair scope and justify it against the causal evidence and the controller scope requirement above.")}

## Rules to reload

The annotation agent must completely reload both annotation skills on every appended iteration, then follow all linked rules and inspect the original blocker evidence above. The main-agent summary prioritizes the repair but does not replace the original evidence or current main-root files.

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

The timing-stage commands are optional telemetry. If used, bracket the real annotation-checking work honestly; they
never replace a check or affect acceptance.

## Completion

Revise the mathematical spec first, editing the case lib only when it is listed as present and writable, then revise C annotations. Never create a missing candidate lib. Use the listed commands when useful for feedback and complete
the semantic annotation review. At the end, success contains only `status: completed`; a blocked result adds one
`blocker` with `failure_class`, `kind`, `location`, `message`, and
`repair_boundary`. Do not copy diff, version, or check results into the report. Notes are optional.
"""


def _annotation_summary_errors(
    state: dict[str, Any],
    attempt: dict[str, Any],
    *,
    input_text: str | None = None,
    attempt_paths: dict[str, Path] | None = None,
) -> list[str]:
    try:
        paths = attempt_paths or _validated_annotation_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        return [str(exc)]
    path = paths["input"]
    if input_text is None:
        try:
            snapshot = _stable_fixed_file_snapshot(
                path,
                owner=paths["directory"],
                label="annotation blocker summary",
            )
            text = _snapshot_text(snapshot, label="annotation blocker summary")
        except (OSError, UnicodeError, ValueError) as exc:
            return [str(exc)]
    else:
        text = input_text
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
            errors.append(
                f"main-agent summary section is empty or too vague: {heading}"
            )
    required_fragments = [
        str(attempt["attempt_id"]),
        str(paths["report"]),
        str(paths["output"]),
        str(state["main_root"]),
        str(attempt.get("retry_reason") or ""),
        ".agents/skills/annotation-filling/SKILL.md",
        ".agents/skills/annotation-checking/SKILL.md",
        _controller_command(state, "symexec", "--round", str(attempt["round"])),
    ]
    if _formal_case_lib_is_active(state):
        required_fragments.append(
            _controller_command(
                state,
                "coq-check",
                "--round",
                str(attempt["round"]),
                "--target-kind",
                "formal-case-lib",
            )
        )
    required_fragments.extend(
        str(state["target_files"][key])
        for key in (
            "c_file",
            "formal_case_lib",
            "proof_manual_file",
            "goal_file",
            "proof_auto_file",
            "goal_check_file",
        )
    )
    for item in attempt.get("feedback_sources", []):
        required_fragments.extend(
            [str(item["phase"]), str(item["attempt_id"]), *item["evidence"]]
        )
    for fragment in required_fragments:
        if fragment not in text:
            errors.append(f"controller-owned summary content was removed: {fragment}")
    if _consider_broader_refactor(attempt) and (
        "consecutive annotation-causal blockers" not in text
    ):
        errors.append(
            "repeated annotation retry must preserve the broader-redesign instruction"
        )
    return errors


def _spec_freeze_section(state: dict[str, Any]) -> str:
    """Render the frozen-specification boundary, or nothing when unfrozen."""

    record = state.get("spec_freeze")
    if not isinstance(record, dict) or not record.get("functions"):
        return ""
    functions = ", ".join(f"`{name}`" for name in record["functions"])
    return f"""
## Frozen specification

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

Controller acceptance re-extracts this surface and compares it entry by entry. A changed or
removed entry fails the attempt and returns here naming the exact entry, so weakening a
frozen specification to make a proof close is not a route forward.
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
    consider_broader_refactor: bool = False,
    feedback_sources: list[dict[str, str]] | None = None,
    retry_reason: str | None = None,
    previous_proving_round: str | None = None,
) -> str:
    if phase == "annotation" and annotation_iteration > 1:
        return _render_annotation_block_summary_template(
            state,
            round_id=round_id,
            attempt_id=attempt_id,
            paths=paths,
            allowed_write_paths=allowed_write_paths,
            previous_attempts=previous_attempts,
            required_lessons=required_lessons,
            annotation_iteration=annotation_iteration,
            consider_broader_refactor=consider_broader_refactor,
            feedback_sources=feedback_sources or [],
            retry_reason=str(retry_reason or "annotation-feedback"),
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
            "This is the initial iteration. Read both annotation skill files completely, follow their linked guides, "
            "and inspect the correct/incorrect examples relevant to this case before editing."
            if annotation_iteration == 1
            else "This is a continuation of the same annotation-agent session. Before editing, reload both annotation "
            "skill files completely and read every listed Markdown and JSON blocker source; do not rely on a summary."
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

The timing-stage commands are optional telemetry. If used, bracket the real annotation-checking work honestly; they
never replace a check or affect acceptance.

## Completion

Design the mathematical spec first, editing `formal_case_lib` only when it is listed as present and writable, then revise C annotations and complete annotation-checking. Never create a missing candidate lib.
Use the listed commands when useful for feedback; controller acceptance reruns every mandatory machine check. Write
a success report containing only `status: completed`; a blocked result adds one
complete `blocker`. Do not copy changed paths, version, or check status into the report.
"""
        )

    goal = state.get("source_goal_version") or {}
    target = state["target_files"]
    manual_path = Path(str(state["main_root"])) / str(target["proof_manual_file"])
    witnesses = [str(item) for item in goal.get("target_witnesses", [])]
    debug_names = [
        name
        for witness in witnesses
        for name in [
            witness,
            *[
                str(item["name"])
                for item in goal.get("split_goals", {}).get(witness, [])
            ],
        ]
    ]
    debug_targets = _fully_qualified_debug_targets(state, manual_path, debug_names)
    witness_lines: list[str] = []
    for name in witnesses:
        split_names = [
            str(item["name"]) for item in goal.get("split_goals", {}).get(name, [])
        ]
        split_text = (
            ", ".join(
                f"`{split_name}` -> `{debug_targets[split_name]}`"
                for split_name in split_names
            )
            if split_names
            else "none"
        )
        witness_lines.append(
            f"- `{name}` -> debug target `{debug_targets[name]}`; "
            f"generated split goals: {split_text}"
        )
    witness_text = "\n".join(witness_lines) if witness_lines else "- none"
    reuse_handoff = _proof_reuse_handoff(
        state,
        round_id=round_id,
        paths=paths,
        previous_round=previous_proving_round,
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

First judge every generated split goal across all target VCs, without analyzing any top-level VC. In this pass, record
only whether each split goal is provable; do not yet plan helpers, proof strategies, or reuse. For a top-level VC with
at least one generated split goal, select `aggressive_pre_process` exactly when all of its split goals are provable; do
not analyze that top-level VC's provability. If any split goal is not provable, or no split goal exists, then judge only
the whole top-level VC's provability and select `LLM_pre_process` when it is provable. If that whole VC is not provable,
report the annotation/specification boundary instead of creating a proving assignment.

After every `proof_mode` is fixed, write the natural-language proof strategy and perform the sealed-source reuse analysis
as one step. For `aggressive_pre_process`, analyze and compare only the split goals; do not write or compare a top-level
proof strategy. For `LLM_pre_process`, analyze and compare only the whole top-level VC. Only after these strategies are
complete, group the top-level VCs by their proof ideas. Never assign a split goal independently: every split goal follows
its parent top-level VC into the same group.

{reuse_handoff}

All formal files are read-only. Form initial groups by invariant, proof pattern, array/frame transformation, refinement
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
plan with an exact Rocq declaration `name`, a short `strategy`, and `visibility` set to `local` or `public`. Historical helpers
from the frozen snapshot or a sealed reuse hint are opportunistic token-identical copies, not new planned-helper declarations. An
owner's local helper still participates in helper-first reuse comparison when it is a current planned helper. Mark a
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
helpers use `{{name, strategy, visibility}}`. Do not copy a version or controller acceptance marker into the plan.
Write the final report: success contains only `status: completed`; a
blocked result adds one `blocker` with `failure_class`, `kind`, `location`, `message`, and `repair_boundary`. Do not
copy the current version or controller checks into the report. Its `failure_class` must be exactly one of
`annotation-gap`, `specification-gap`, `dependency-gap`, `source-version`, `plan-defect`, `report-defect`, or
`infrastructure`. The controller routes the first four to annotation and the last three to a same-phase vc-checking
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
    annotation_causal_retry_count: int = 0,
) -> dict[str, Any]:
    state["waiting_for"] = []
    report_root = Path(str(state["report_root"]))
    round_id = _next_round_id(state, phase)
    attempt_id = f"{round_id}-attempt-{attempt_index}"
    if phase == "annotation":
        if (
            isinstance(annotation_causal_retry_count, bool)
            or not isinstance(annotation_causal_retry_count, int)
            or annotation_causal_retry_count < 0
        ):
            raise ValueError("annotation causal retry count must be non-negative")
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
        annotation_causal_retry_count = 0
    consider_broader_refactor = annotation_causal_retry_count >= 2
    source = _source_version_for_state(state, annotated=phase != "annotation")
    target = state["target_files"]
    previous_proving_round = (
        _latest_reusable_vc_proving_round(state) if phase == "vc-checking" else None
    )
    allowed = []
    if phase == "annotation":
        allowed = [target["c_file"]]
        if _formal_case_lib_is_active(state):
            allowed.append(target["formal_case_lib"])
        allowed.extend(target[key] for key in GENERATED_KEYS)
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
            consider_broader_refactor=consider_broader_refactor,
            feedback_sources=feedback_sources or [],
            retry_reason=retry_reason,
            previous_proving_round=previous_proving_round,
        ),
    )
    goal_digest = (
        str((state.get("source_goal_version") or {}).get("digest") or "") or None
    )
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
        "status": "awaiting-main-summary"
        if phase == "annotation" and annotation_iteration > 1
        else "prepared",
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
    if phase == "vc-checking" and previous_proving_round is not None:
        attempt["proof_reuse_round"] = previous_proving_round
    if phase == "annotation":
        history = annotation_history_root(
            Path(str(state["run_root"]))
        ) / annotation_attempt_directory_name(annotation_iteration)
        attempt["annotation_history_directory"] = str(history)
        attempt["annotation_iteration"] = annotation_iteration
        attempt["annotation_causal_retry_count"] = annotation_causal_retry_count
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
                    "consider_broader_refactor": consider_broader_refactor,
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
                    "consider_broader_refactor": consider_broader_refactor,
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
        "source_goal_version": str(state["source_goal_version"]["digest"]),
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


def _reusable_group_ids(attempt: dict[str, Any], manifest: dict[str, Any]) -> set[str]:
    all_ids = {
        str(group.get("id") or "")
        for group in manifest.get("groups", [])
        if isinstance(group, dict) and group.get("id")
    }
    record = attempt.get("reuse_group_artifacts")
    valid = (
        record.get("structurally_valid_groups") if isinstance(record, dict) else None
    )
    return (
        {str(group_id) for group_id in valid} & all_ids
        if isinstance(valid, list)
        else all_ids
    )


def _seal_failed_proving_reuse_artifacts(
    state: dict[str, Any],
    attempt: dict[str, Any],
    groups: list[dict[str, Any]],
    *,
    require_finalized: bool = False,
) -> None:
    """Seal every group file before a failed proving round can feed reuse."""

    if isinstance(attempt.get("reuse_group_artifacts"), dict):
        if require_finalized:
            reuse_groups = attempt["reuse_group_artifacts"].get("groups")
            for group in groups:
                group_id = str(group["id"])
                group_state = attempt.get("groups", {}).get(group_id, {})
                finalized_seal = (
                    group_state.get("accepted_artifact_sha256")
                    if isinstance(group_state, dict)
                    and group_state.get("status") == "accepted"
                    else group_state.get("artifact_sha256")
                    if isinstance(group_state, dict)
                    else None
                )
                if (
                    not isinstance(reuse_groups, dict)
                    or reuse_groups.get(group_id) != finalized_seal
                    or (
                        isinstance(group_state, dict)
                        and group_state.get("status") == "blocked"
                        and (
                            not isinstance(finalized_seal, dict)
                            or "output" not in finalized_seal
                        )
                    )
                ):
                    raise SystemExit(
                        "finalized vc-proving reuse seal differs from its group delivery"
                    )
            if not _reuse_group_artifacts_are_sealed(attempt, groups):
                raise SystemExit(
                    "finalized vc-proving reuse artifacts changed after sealing"
                )
        return
    sealed: dict[str, dict[str, str]] = {}
    for group in groups:
        group_id = str(group["id"])
        try:
            group_state = attempt.get("groups", {}).get(group_id, {})
            finalized_seal = (
                group_state.get("accepted_artifact_sha256")
                if isinstance(group_state, dict)
                and group_state.get("status") == "accepted"
                else group_state.get("artifact_sha256")
                if isinstance(group_state, dict)
                else None
            )
            if require_finalized:
                if (
                    not isinstance(group_state, dict)
                    or group_state.get("status") not in {"accepted", "blocked"}
                    or (
                        group_state.get("status") == "blocked"
                        and (
                            not isinstance(finalized_seal, dict)
                            or "output" not in finalized_seal
                        )
                    )
                    or not _group_artifact_seal_matches(group, finalized_seal)
                ):
                    raise ValueError(
                        "group did not reach a sealed accepted/blocked terminal state"
                    )
                sealed[group_id] = {
                    name: str(digest)
                    for name, digest in finalized_seal.items()
                }
            else:
                sealed[group_id] = {
                    name: str(digest)
                    for name, digest in _group_artifact_digests(group).items()
                }
        except (OSError, TypeError, ValueError) as exc:
            raise SystemExit(
                "cannot seal failed vc-proving reuse source; invalid group artifacts: "
                f"{group_id}: {exc}"
            ) from exc
    try:
        seed_root = _validated_reuse_raw_root(state, attempt)
    except (OSError, TypeError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    structurally_valid_groups: list[str] = []
    invalid_groups: dict[str, str] = {}
    for group in groups:
        group_id = str(group["id"])
        try:
            validation = validate_group_for_acceptance_result(
                Path(str(attempt["group_workers_manifest"])),
                group_id=group_id,
                main_root=Path(str(state["main_root"])),
                expected_proof_manual=str(state["target_files"]["proof_manual_file"]),
                expected_formal_case_lib=str(state["target_files"]["formal_case_lib"]),
                require_complete=False,
                seed_root=seed_root,
                expected_run_root=Path(str(state["run_root"])),
                expected_round=str(attempt["round"]),
                forbidden_modules=_generated_artifact_module_spellings_for_state(
                    state,
                    source_goal_version=state["source_goal_version"],
                ),
            )
            validation_errors = [str(item) for item in validation.get("errors", [])]
        except (OSError, UnicodeDecodeError, ValueError, SystemExit) as exc:
            validation_errors = [str(exc)]
        if validation_errors:
            invalid_groups[group_id] = validation_errors[0]
        else:
            structurally_valid_groups.append(group_id)
    attempt["reuse_group_artifacts"] = {
        "sealed_at": _utc(),
        "groups": sealed,
        "structurally_valid_groups": structurally_valid_groups,
        "invalid_groups": invalid_groups,
    }


def _reuse_group_artifacts_are_sealed(
    attempt: dict[str, Any], groups: list[dict[str, Any]]
) -> bool:
    record = attempt.get("reuse_group_artifacts")
    expected_groups = record.get("groups") if isinstance(record, dict) else None
    if not isinstance(expected_groups, dict):
        return False
    if set(expected_groups) != {str(group["id"]) for group in groups}:
        return False
    for group in groups:
        expected = expected_groups.get(str(group["id"]))
        if not _group_artifact_seal_matches(group, expected):
            return False
    return True


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
                "location": str(blocker["location"]),
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
            f"{attempt['round']}:{str(pending_promotion.get('group_id') or '')}"
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
            # Version drift invalidates the accepted annotation that all groups
            # share.  Do not start the remaining prepared workers and do not
            # misroute this as a plan/report retry: return the machine-detected
            # drift through the existing persistent annotation feedback path.
            drift_receipt = attempt["groups"][stale_group].get("version_drift")
            state["current_blockers"] = [
                drift_receipt
                if isinstance(drift_receipt, dict)
                else {
                    "failure_class": "current-version-drift",
                    "round": str(attempt["round"]),
                    "group_id": stale_group,
                    "message": str(
                        attempt["groups"][stale_group].get("stale_reason")
                        or "group became stale after current-source drift"
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
            # Compact exhaustion stops this run, but a later explicitly
            # requested vc-checking round may still compare structurally valid
            # proof ideas from the immediately preceding failed round.  Seal
            # the fixed group files before returning, just as for an ordinary
            # blocked group; otherwise the selector's existing
            # compact-error-retry-exhausted route can never be reached.
            _seal_failed_proving_reuse_artifacts(state, attempt, groups)
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
            # Never turn changed or missing sealed bytes into a new reuse
            # source. Owner-editable report mistakes have already gone through
            # repair-prepared; reaching this branch requires controller/manual
            # intervention.
            return
        _seal_failed_proving_reuse_artifacts(state, attempt, groups)
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
            blocker_text = json.dumps(group_blockers, sort_keys=True).lower()
            plan_failure = any(
                marker in blocker_text
                for marker in (
                    "vc-plan",
                    "proof-mode",
                    "proof mode",
                    "group-boundary",
                    "route unusable",
                )
            )
            retry_phase = "vc-checking" if plan_failure else "annotation"
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
                    }
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
        # they do not cancel sibling work.  Only after the accepted plan has
        # reached accepted/annotation-blocked terminal states do we freeze the
        # full round for conditional reuse and publish one annotation retry.
        _seal_failed_proving_reuse_artifacts(
            state,
            attempt,
            groups,
            require_finalized=True,
        )
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
    for group_id in manifest.get("dispatch_order", manifest.get("order", [])):
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


def annotation_summary_ready(args: argparse.Namespace) -> int:
    """Validate and seal the main-written blocker summary before agent append."""

    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = state.get("attempts", {}).get(args.attempt)
    if not isinstance(attempt, dict) or attempt.get("phase") != "annotation":
        raise SystemExit(f"annotation attempt not found: {args.attempt}")
    session = state.get("annotation_session")
    if not isinstance(session, dict) or session.get("current_attempt") != args.attempt:
        raise SystemExit(
            "annotation summary does not belong to the current persistent session attempt"
        )
    if attempt.get("status") != "awaiting-main-summary":
        raise SystemExit(
            f"annotation attempt is not awaiting a main-agent summary: {attempt.get('status')}"
        )
    try:
        attempt_paths = _validated_annotation_attempt_paths(state, attempt)
        input_snapshot = _stable_fixed_file_snapshot(
            attempt_paths["input"],
            owner=attempt_paths["directory"],
            label="annotation blocker summary",
        )
        input_text = _snapshot_text(
            input_snapshot,
            label="annotation blocker summary",
        )
    except (OSError, UnicodeError, ValueError) as exc:
        print(json.dumps({"status": "invalid", "errors": [str(exc)]}, indent=2))
        return 1
    # Import locally to avoid changing the controller modules' existing load
    # order while reusing the same sealed-source check used at annotation claim.
    from controller_attempts import _feedback_source_reference_errors

    errors = [
        *_feedback_source_reference_errors(state, attempt),
        *_annotation_summary_errors(
            state,
            attempt,
            input_text=input_text,
            attempt_paths=attempt_paths,
        ),
    ]
    if errors:
        print(json.dumps({"status": "invalid", "errors": errors}, indent=2))
        return 1
    attempt["input_sha256"] = str(input_snapshot["sha256"])
    attempt["status"] = "prepared"
    session["status"] = "prepared"
    state["next_actions"] = [
        {
            "id": f"append-{attempt['attempt_id']}",
            "kind": "append-annotation-agent",
            "phase": "annotation",
            "session_id": session["session_id"],
            "attempt_id": attempt["attempt_id"],
            "input": str(attempt_paths["input"]),
            "report": str(attempt_paths["report"]),
            "feedback_sources": attempt.get("feedback_sources", []),
            "consider_broader_refactor": _consider_broader_refactor(attempt),
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


def _dune_gate_errors(state: dict[str, Any]) -> list[str]:
    source_goal = state.get("source_goal_version")
    digest = str(
        source_goal.get("digest") if isinstance(source_goal, dict) else ""
    )
    if not digest:
        return ["accepted annotation has no source_goal_version"]
    return dune_preparation_receipt_errors(
        workspace_root=Path(str(state["main_root"])),
        receipt=(
            state.get("dune_preparation")
            if isinstance(state.get("dune_preparation"), dict)
            else None
        ),
        expected_source_goal_version=digest,
    )


def _queue_dune_gate(state: dict[str, Any]) -> None:
    state["phase"] = "dune-build"
    state["next_actions"] = [_preparation_action(state)]
    state["waiting_for"] = []


def _target_witnesses(state: dict[str, Any]) -> list[str]:
    source_goal = state.get("source_goal_version")
    if not isinstance(source_goal, dict):
        return []
    witnesses = source_goal.get("target_witnesses")
    return [str(item) for item in witnesses] if isinstance(witnesses, list) else []


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
            "pre-VC current-version drift has no accepted annotation attempt"
        )
    blocker = {
        "failure_class": "current-version-drift",
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
            "reason": "dune-preparation-source-drift",
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
    # it, especially after a version gate has just routed back to annotation.
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
            version_errors = _current_version_errors(state)
            if version_errors:
                state["phase"] = "dune-build"
                _queue_pre_vc_annotation_drift(state, version_errors)
            elif _dune_gate_errors(state):
                _queue_dune_gate(state)
            else:
                _advance_after_dune_build(state)
        elif _current_attempt(state, "annotation") is None:
            _init_round_attempt(state, phase="annotation")
    elif phase == "dune-build":
        version_errors = _current_version_errors(state)
        if version_errors:
            _queue_pre_vc_annotation_drift(state, version_errors)
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
