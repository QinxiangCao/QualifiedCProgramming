"""Run facts and deterministic paths. Scheduling is derived, never persisted."""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from build_mode import detect_build_mode
from file_integrity import _lexical_regular_file_snapshot, _snapshot_text
from path_utils import (
    ANNOTATION_ATTEMPTS_DIR_NAME, ANNOTATION_HISTORY_DIR_NAME,
    annotation_attempt_directory_name, controller_state_path, ensure_run_root,
    fixed_path_under, group_build_workspace, is_run_root_name, main_root_from_run_root,
    reports_root, run_logs_path, slug, target_files_for_c, write_bytes, write_json,
)
from proof_manual_utils import generated_artifact_module_spellings, manual_vc_index
from spec_freeze import extract_lib, extract_spec_surface
from symexec_tooling import symexec_profile_record, symexec_profile_for_state

GENERATED_KEYS = ("goal_file", "proof_auto_file", "proof_manual_file", "goal_check_file")
CONTROLLER_STATE_SCHEMA_VERSION = 4
WINDOWS_LEGACY_DIRECTORY_PATH_LIMIT = 248
WINDOWS_LEGACY_FILE_PATH_LIMIT = 260
PHASES = {"intake", "annotation", "dependencies", "vc-checking", "vc-proving", "final-apply", "final-check", "done"}
TASK_PHASES = ("annotation", "vc-checking", "vc-proving")
TASK_STATUSES = {"prepared", "running", "returned", "accepted", "blocked"}
FAILED_VC_FIELDS = {"source_attempt", "name", "parent", "annotation_location", "manual", "message"}
FORMAL_CASE_LIB_SEED = "From Coq Require Import ZArith List.\nImport ListNotations.\nLocal Open Scope Z_scope.\n"

def _utc() -> str:
    return (
        datetime.now(UTC)
        .isoformat(timespec="microseconds")
        .replace("+00:00", "Z")
    )

def _parse_utc(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))

def _elapsed_between(started_at: str, finished_at: str) -> float:
    return round(
        max(0.0, (_parse_utc(finished_at) - _parse_utc(started_at)).total_seconds()), 6
    )

def _windows_long_paths_enabled() -> bool:
    """Read the machine switch required by long-path-aware Windows tools."""

    if os.name != "nt":
        return True
    try:
        import winreg

        with winreg.OpenKey(
            winreg.HKEY_LOCAL_MACHINE,
            r"SYSTEM\CurrentControlSet\Control\FileSystem",
        ) as key:
            value, _value_type = winreg.QueryValueEx(key, "LongPathsEnabled")
        return int(value) == 1
    except (OSError, TypeError, ValueError):
        return False

def _windows_path_length_error(
    *,
    main_root: Path,
    projected_run_name: str,
    target_files: dict[str, str],
    file_limit: int = WINDOWS_LEGACY_FILE_PATH_LIMIT,
    directory_limit: int = WINDOWS_LEGACY_DIRECTORY_PATH_LIMIT,
) -> str | None:
    """Reject a run whose known deepest file cannot use legacy Windows paths."""

    formal_relatives = [
        Path(str(target_files[field]))
        for field in (
            "formal_case_lib",
            "goal_file",
            "proof_auto_file",
            "proof_manual_file",
            "goal_check_file",
        )
    ]
    longest_formal = max(formal_relatives, key=lambda item: len(os.fspath(item)))
    case_name = str(target_files["case_name"])
    run_root = main_root / "verification_runs" / projected_run_name
    report_root = main_root / "reports" / projected_run_name
    proving_round = f"{case_name}-vc-proving-r10"
    checking_round = f"{case_name}-vc-checking-r10"
    candidates = {
        "formal target": main_root / longest_formal,
        "annotation history": (
            run_root
            / ANNOTATION_HISTORY_DIR_NAME
            / annotation_attempt_directory_name(10)
            / "after"
            / longest_formal
        ),
        "vc-checking build": (
            run_root
            / "_coq_builds"
            / checking_round
            / "vc-checking"
            / "src"
            / longest_formal
        ),
        "group development build": group_build_workspace(run_root, proving_round, "group_9999__projection").parent / "dev" / longest_formal,
        "annotation generation": report_root / ANNOTATION_ATTEMPTS_DIR_NAME / annotation_attempt_directory_name(10) / ".gen-xxxxxxxx" / longest_formal,
        "final replay": report_root / "final-check" / "symexec-refresh" / longest_formal,
        "final apply build": run_root / "_coq_builds" / "final-apply" / "src" / longest_formal,
        "parent build": (
            run_root
            / "_coq_builds"
            / proving_round
            / "parent"
            / "src"
            / longest_formal
        ),
        "final build": (
            run_root / "_coq_builds" / "final-check" / "src" / longest_formal
        ),
        "final backup": report_root / "final-check" / "backup" / "proof_manual_file.candidate",
    }
    violations: list[tuple[int, str, str, Path, int, int]] = []
    for label, candidate in candidates.items():
        file_length = len(os.fspath(candidate))
        if file_length >= file_limit:
            violations.append(
                (
                    file_length - file_limit,
                    label,
                    "file",
                    candidate,
                    file_length,
                    file_limit,
                )
            )
        parent = candidate.parent
        directory_length = len(os.fspath(parent))
        if directory_length >= directory_limit:
            violations.append(
                (
                    directory_length - directory_limit,
                    label,
                    "directory",
                    parent,
                    directory_length,
                    directory_limit,
                )
            )
    if not violations:
        return None
    _excess, label, path_kind, longest, length, limit = max(violations)
    return (
        "Windows long paths are disabled and the projected "
        f"{label} {path_kind} is {length} characters "
        f"(limit {limit - 1}): {longest}. "
        "Use a shorter root, or enable long paths and verify all selected tools support them; "
        "do not use subst, junctions, or aliases."
    )



def _freeze_spec_functions(args: argparse.Namespace) -> list[str]:
    """Flatten repeated and comma-separated --freeze-spec values."""

    return [
        name.strip()
        for value in getattr(args, "freeze_spec", []) or []
        for name in str(value).split(",")
        if name.strip()
    ]

def _spec_freeze_baseline(
    *,
    main_root: Path,
    target_files: dict[str, str],
    functions: list[str],
) -> dict[str, Any] | None:
    """Capture the specification surface that this run may not change.

    Returns ``None`` when no function was frozen, which is the default: the
    annotation agent then authors specifications freely and no comparison runs.
    """

    if not functions:
        return None
    c_file = main_root / target_files["c_file"]
    lib_file = main_root / target_files["formal_case_lib"]
    frozen_functions = sorted(set(functions))
    baseline = extract_spec_surface(c_file, lib_file)
    spec_functions = {
        str(key).split("::", 1)[0]
        for key in baseline.get("specs", {})
        if "::" in str(key)
    }
    missing = [name for name in frozen_functions if name not in spec_functions]
    if missing:
        raise SystemExit(
            "--freeze-spec did not match an extracted function specification: "
            + ", ".join(missing)
        )
    return {
        "functions": frozen_functions,
        "baseline": baseline,
    }

def _problem_context_from_args(args: argparse.Namespace) -> dict[str, Any]:
    statement_parts: list[str] = []
    if args.problem_statement:
        statement_parts.append(str(args.problem_statement))
    if args.problem_statement_file:
        statement_file = Path(args.problem_statement_file).expanduser().resolve()
        if not statement_file.is_file():
            raise SystemExit(f"problem statement file not found: {statement_file}")
        statement_parts.append(statement_file.read_text(encoding="utf-8"))
    raw = {
        "problem_statement": "\n\n".join(
            part.strip() for part in statement_parts if part.strip()
        ),
        "target_function": str(args.target_function or ""),
        "expected_behavior": str(args.expected_behavior or ""),
        "input_output_contract": str(args.input_output_contract or ""),
        "spec_hint": [str(item) for item in args.spec_hint],
        "preferred_hidden_properties": [
            str(item) for item in args.preferred_hidden_property
        ],
        "forbidden_patterns": [str(item) for item in args.forbidden_pattern],
        "reference_case_hints": [str(item) for item in args.reference_case_hint],
    }
    return {key: value for key, value in raw.items() if value not in ("", [], None)}

def _json_load(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(_snapshot_text(_lexical_regular_file_snapshot(
        root=path.parent, relative=path.name, label="JSON input"), label="JSON input"))


def _run_root_from_id(main_root: Path, run_id: str) -> Path:
    if not isinstance(run_id, str) or Path(run_id).name != run_id or not is_run_root_name(run_id):
        raise SystemExit(f"invalid run id: {run_id}")
    path = fixed_path_under(main_root / "verification_runs" / run_id, main_root, label="run root")
    if not path.is_dir():
        raise SystemExit(f"run not found: {path}")
    return path


def load_run(args: argparse.Namespace) -> dict[str, Any]:
    root = Path(args.main_root).expanduser().absolute() if args.main_root else Path.cwd()
    return _load_state(_run_root_from_id(root, args.run))


def current_attempt(state: dict, phase: str) -> dict | None:
    identifier = state["current"].get(phase)
    return state["attempts"].get(identifier) if identifier else None


def require_attempt(state: dict, identifier: str, phase: str | None = None) -> dict:
    task = state["attempts"].get(identifier)
    if not isinstance(task, dict) or state["current"].get(task["phase"]) != identifier:
        raise SystemExit(f"attempt is not current: {identifier}")
    if phase is not None and task["phase"] != phase:
        raise SystemExit(f"attempt is not a {phase} task: {identifier}")
    return task


def attempt_paths(state: dict, attempt: dict) -> dict[str, Path]:
    identifier = attempt["attempt_id"]
    phase = attempt["phase"]
    prefix = f"{state['case']}-{phase}-r"
    if phase not in TASK_PHASES or not identifier.startswith(prefix) or not identifier[len(prefix):].isdigit():
        raise ValueError(f"invalid task identity: {identifier}")
    iteration = int(identifier[len(prefix):])
    if iteration < 1:
        raise ValueError("task number must be positive")
    report_root = Path(state["report_root"])
    run_root = Path(state["run_root"])
    if phase == "annotation":
        directory = report_root / ANNOTATION_ATTEMPTS_DIR_NAME / annotation_attempt_directory_name(iteration)
    else:
        directory = report_root / "rounds" / identifier
    paths = {"directory": directory, "input": directory / "agent_input.md",
             "report": directory / "agent_report.json", "output": directory / "agent_output.md"}
    if phase == "annotation":
        history = run_root / ANNOTATION_HISTORY_DIR_NAME / annotation_attempt_directory_name(iteration)
        paths.update(plan=directory / "annotation_plan.json", history=history,
                     before=history / "before", after=history / "after")
    elif phase == "vc-checking":
        paths.update(group_plan=directory / "group_plan.json",
                     debug_manual=directory / Path(state["target_files"]["proof_manual_file"]).name)
    else:
        paths.update(workspace=run_root / identifier, merged=run_root / identifier / "proving_merged")
    return {role: fixed_path_under(path, Path(state["main_root"]), label=f"task {role}")
            for role, path in paths.items()}


def _failed_vcs_errors(value: Any, *, run_root: Path | None = None) -> list[str]:
    if not isinstance(value, list):
        return ["failed_vcs must be a list"]
    seen = set()
    for item in value:
        if not isinstance(item, dict) or set(item) != FAILED_VC_FIELDS:
            return ["failed_vcs entries require exact fields"]
        if any(not isinstance(item[key], str) or not item[key].strip() for key in FAILED_VC_FIELDS - {"parent"}):
            return ["failed_vcs text fields must be non-empty strings"]
        if item["parent"] is not None and (not isinstance(item["parent"], str) or not item["parent"]):
            return ["failed_vcs parent must be null or a non-empty string"]
        identity = (item["source_attempt"], item["name"])
        if identity in seen:
            return ["failed_vcs repeats a source VC"]
        seen.add(identity)
        if run_root is not None:
            try:
                path = Path(item["manual"])
                if not path.is_absolute():
                    return ["failed_vcs manual must be absolute"]
                fixed_path_under(path, run_root, label="historical manual")
            except SystemExit as exc:
                return [str(exc)]
    return []


def validate_state(state: Any, run_root: Path | None = None) -> list[str]:
    if not isinstance(state, dict) or state.get("schema_version") != CONTROLLER_STATE_SCHEMA_VERSION:
        return ["This run uses an older controller contract; use its original code or initialize a new run."]
    try:
        fields = {"schema_version", "generation", "run_id", "case", "phase", "main_root", "run_root", "report_root",
                  "target_files", "problem_context", "formal_case_lib_policy", "spec_freeze", "run_control",
                  "symexec_profile", "max_witnesses_per_group", "max_parallel_group_workers", "dune_preparation",
                  "attempts", "current", "annotation_owner", "pending_retry", "current_blockers", "final_candidate",
                  "final_apply", "final_check", "created_at"}
        if fields - state.keys() or state.keys() - fields - {"updated_at", "finished_at", "final_apply_transaction"}:
            raise ValueError("unsupported or missing state fields")
        if not isinstance(state["current_blockers"], list) or not all(isinstance(item, dict) for item in state["current_blockers"]):
            raise ValueError("current_blockers must be a list of objects")
        retry = state["pending_retry"]
        if retry is not None and (not isinstance(retry, dict) or set(retry) != {"phase", "reason", "previous_attempt"}
                or retry["phase"] not in {"annotation", "vc-checking"} or not all(isinstance(value, str) and value for value in retry.values())):
            raise ValueError("invalid pending retry")
        if re.fullmatch(rf"{re.escape(slug(state['case']))}-\d{{14}}(?:-\d{{2}})?", state["run_id"]) is None:
            raise ValueError("run id differs from its case identity")
        root = Path(state["main_root"])
        if not root.is_absolute():
            raise ValueError("main_root must be absolute")
        fixed_path_under(root, root, label="main root")
        expected_run = fixed_path_under(root / "verification_runs" / state["run_id"], root, label="run root")
        if not is_run_root_name(state["run_id"]) or expected_run.name != state["run_id"]:
            raise ValueError("invalid run identity")
        if run_root is not None and expected_run != run_root:
            raise ValueError("state belongs to a different run")
        if state["run_root"] != str(expected_run) or state["report_root"] != str(root / "reports" / state["run_id"]):
            raise ValueError("run/report paths must match run identity")
        if state["target_files"] != target_files_for_c(state["target_files"]["c_file"], state["case"]):
            raise ValueError("target_files differs from canonical C/case mapping")
        for key in ("c_file", "formal_directory", "formal_case_lib", *GENERATED_KEYS):
            fixed_path_under(root / state["target_files"][key], root, label=key)
        if state["phase"] not in PHASES or set(state["current"]) != set(TASK_PHASES):
            raise ValueError("invalid phase/current tasks")
        if type(state["generation"]) is not int or state["generation"] < 0:
            raise ValueError("invalid state generation")
        for key in ("max_witnesses_per_group", "max_parallel_group_workers"):
            if type(state[key]) is not int or state[key] < 1:
                raise ValueError(f"{key} must be positive")
        if state["formal_case_lib_policy"] not in {"present", "create", "absent"}:
            raise ValueError("invalid library policy")
        if state["run_control"]["status"] not in {"active", "paused"}:
            raise ValueError("invalid run control")
        symexec_profile_for_state(state)
        if not isinstance(state["attempts"], dict):
            raise ValueError("attempts must be an object")
        for identifier, task in state["attempts"].items():
            if identifier != task["attempt_id"] or task["status"] not in TASK_STATUSES:
                raise ValueError("invalid task identity/status")
            attempt_paths(state, task)
            if task["phase"] == "annotation":
                errors = _failed_vcs_errors(task.get("failed_vcs", []), run_root=expected_run)
                if errors:
                    raise ValueError(errors[0])
            for owner_task in [task, *task.get("groups", {}).values()]:
                if owner_task["status"] not in TASK_STATUSES:
                    raise ValueError("invalid owner task status")
                if type(owner_task.get("repair_index", 0)) is not int or owner_task.get("repair_index", 0) < 0:
                    raise ValueError("invalid repair index")
                if owner_task.get("owner") is not None and not isinstance(owner_task["owner"], str):
                    raise ValueError("invalid task owner")
        for phase, identifier in state["current"].items():
            if identifier is not None and state["attempts"][identifier]["phase"] != phase:
                raise ValueError("current task has wrong phase")
    except (KeyError, TypeError, ValueError, OSError, SystemExit) as exc:
        return [f"invalid controller state: {exc}"]
    return []


def _load_state(run_root: Path) -> dict:
    path = fixed_path_under(controller_state_path(run_root), main_root_from_run_root(run_root), label="controller state")
    state = _json_load(path)
    errors = validate_state(state, run_root)
    if errors:
        raise SystemExit(errors[0])
    return state


def _save_state(run_root: Path, state: dict) -> None:
    errors = validate_state(state, run_root)
    if errors:
        raise SystemExit(errors[0])
    path = fixed_path_under(controller_state_path(run_root), Path(state["main_root"]), label="controller state")
    current = _json_load(path)
    if current is not None and current["generation"] != state["generation"]:
        raise SystemExit("controller state changed during this command; reload before writing")
    # ponytail: main is the single business-state writer; this is not an interprocess CAS.
    state["generation"] += 1
    state["updated_at"] = _utc()
    write_json(path, state)


def _append_log(run_root: Path, record: dict) -> None:
    path = fixed_path_under(run_logs_path(run_root), main_root_from_run_root(run_root), label="run log")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(record, ensure_ascii=True) + "\n")


def _append_event(run_root: Path, state: dict, event: str, **details: Any) -> None:
    try:
        _append_log(run_root, {"at": _utc(), "phase": state["phase"], "event": event, "details": details})
    except (OSError, ValueError, SystemExit) as exc:
        print(f"Run log diagnostic: {exc}", file=sys.stderr)

def _formal_case_lib_is_active(state: dict[str, Any]) -> bool:
    """Return whether this run has an editable canonical case library."""

    policy = state.get("formal_case_lib_policy")
    if policy not in {"present", "create", "absent"}:
        raise ValueError("formal_case_lib policy is invalid")
    return policy != "absent"

def _formal_case_lib_snapshot(state: dict[str, Any]) -> dict[str, Any]:
    """Snapshot the exact optional case-lib leaf without following links."""

    return _lexical_regular_file_snapshot(
        root=Path(str(state["main_root"])),
        relative=str(state["target_files"]["formal_case_lib"]),
        label="formal_case_lib candidate",
    )


def _generated_artifact_module_spellings_for_state(
    state: dict[str, Any],
) -> frozenset[str]:
    """Return exact generated modules that currently exist in the main root."""

    target = state["target_files"]
    main_root = Path(str(state["main_root"]))
    present_roles: set[str] = set()
    for role in GENERATED_KEYS:
        snapshot = _lexical_regular_file_snapshot(
            root=main_root,
            relative=str(target[role]),
            label=f"generated module boundary {role}",
        )
        artifact_state = snapshot.get("state")
        if artifact_state == "missing":
            continue
        if artifact_state != "present":
            detail = str(
                snapshot.get("message") or "invalid generated artifact topology"
            )
            raise ValueError(
                f"generated module boundary cannot classify {role}: {detail}"
            )
        present_roles.add(role)
    return generated_artifact_module_spellings(target, roles=present_roles)

def _manual_obligations(state: dict[str, Any]) -> dict[str, Any]:
    """Read the complete VC index from the current main-root manual."""

    snapshot = _lexical_regular_file_snapshot(
        root=Path(str(state["main_root"])),
        relative=str(state["target_files"]["proof_manual_file"]),
        label="current proof manual",
    )
    if snapshot.get("state") == "missing":
        return {
            "by_name": {},
            "top_level": [],
            "split_goals": {},
        }
    text = _snapshot_text(snapshot, label="current proof manual")
    return manual_vc_index(text)

def _current_files_errors(state: dict[str, Any]) -> list[str]:
    """Validate readable current inputs, without comparing earlier revisions."""

    errors: list[str] = []
    for role in ("c_file", "formal_case_lib", *GENERATED_KEYS):
        snapshot = _lexical_regular_file_snapshot(
            root=Path(state["main_root"]), relative=state["target_files"][role], label=f"current {role}"
        )
        if role == "formal_case_lib" and not _formal_case_lib_is_active(state) and snapshot["state"] != "missing":
            errors.append("formal_case_lib must remain absent under the current run policy")
            continue
        optional = role == "proof_manual_file" or (role == "formal_case_lib" and not _formal_case_lib_is_active(state))
        if snapshot["state"] == "missing" and optional:
            continue
        try:
            _snapshot_text(snapshot, label=f"current {role}")
        except ValueError as exc:
            errors.append(str(exc))
    return errors

def _archive_annotation_stage(state: dict, attempt: dict, stage: str) -> None:
    if stage not in {"before", "after"}:
        raise ValueError("unknown annotation history stage")
    destination = attempt_paths(state, attempt)[stage]
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir(parents=True)
    for role in ("c_file", "formal_case_lib", *GENERATED_KEYS):
        relative = state["target_files"][role]
        snapshot = _lexical_regular_file_snapshot(root=Path(state["main_root"]), relative=relative, label=role)
        if snapshot["state"] == "missing":
            continue
        if snapshot["state"] != "present":
            raise ValueError(snapshot.get("message", f"unreadable {role}"))
        write_bytes(fixed_path_under(destination / relative, destination, label="history copy"), snapshot["data"])

def _timing_path(report_root: Path) -> Path:
    return report_root / "timing_summary.json"

def _record_timing_interval(
    attempt: dict[str, Any],
    stage: str,
    *,
    started_at: str,
    finished_at: str | None = None,
    elapsed_seconds: float | None = None,
) -> dict[str, Any]:
    interval: dict[str, Any] = {"started_at": started_at}
    if finished_at is not None:
        interval["finished_at"] = finished_at
        interval["elapsed_seconds"] = round(
            float(elapsed_seconds)
            if elapsed_seconds is not None
            else _elapsed_between(started_at, finished_at),
            6,
        )
    attempt.setdefault("timing", {}).setdefault(stage, []).append(interval)
    return interval

def _record_elapsed_stage(
    attempt: dict[str, Any], stage: str, elapsed_seconds: float
) -> None:
    finished = datetime.now(UTC)
    started = finished.timestamp() - max(0.0, float(elapsed_seconds))
    _record_timing_interval(
        attempt,
        stage,
        started_at=datetime.fromtimestamp(started, UTC)
        .isoformat(timespec="microseconds")
        .replace("+00:00", "Z"),
        finished_at=finished.isoformat(timespec="microseconds").replace("+00:00", "Z"),
        elapsed_seconds=elapsed_seconds,
    )

def _aggregate_stage(
    name: str, intervals: list[dict[str, Any]]
) -> dict[str, Any] | None:
    if not intervals:
        return None
    starts = [str(item["started_at"]) for item in intervals if item.get("started_at")]
    if not starts:
        return None
    finished = [
        str(item["finished_at"]) for item in intervals if item.get("finished_at")
    ]
    stage: dict[str, Any] = {
        "name": name,
        "started_at": min(starts, key=_parse_utc),
    }
    if len(intervals) > 1:
        stage["calls"] = len(intervals)
    if len(finished) == len(intervals):
        stage["finished_at"] = max(finished, key=_parse_utc)
        stage["elapsed_seconds"] = round(
            sum(float(item.get("elapsed_seconds", 0.0)) for item in intervals), 6
        )
    return stage

def _lifecycle_stage(
    name: str, started_at: str | None, finished_at: str | None
) -> dict[str, Any] | None:
    if not started_at:
        return None
    stage: dict[str, Any] = {"name": name, "started_at": started_at}
    if finished_at:
        stage["finished_at"] = finished_at
        stage["elapsed_seconds"] = _elapsed_between(started_at, finished_at)
    return stage

def _timing_entry(attempt: dict[str, Any], measurements: dict[str, list]) -> dict[str, Any]:
    entry = {key: attempt[key] for key in ("attempt_id", "phase", "status")}
    lifecycle = _lifecycle_stage("owner-work", attempt.get("started_at"), attempt.get("returned_at"))
    stages = []
    # Keep recorded intervals as data. Do not infer repair categories or retry identities.
    timing = {name: list(intervals) for name, intervals in attempt.get("timing", {}).items()}
    if lifecycle:
        timing.setdefault("owner-work", []).append(lifecycle)
    for group in attempt.get("groups", {}).values():
        timing.setdefault("group-work", []).extend(group.get("timing", {}).get("owner-work", []))
        if group.get("started_at"):
            timing["group-work"].append({"started_at": group["started_at"]})
    for name, intervals in measurements.items():
        timing.setdefault(name, []).extend(intervals)
    for name, intervals in sorted(timing.items()):
        stage = _aggregate_stage(name, intervals)
        if stage is not None:
            stages.append(stage)
    entry["stages"] = stages
    return entry

def _write_timing_summary(state: dict[str, Any]) -> None:
    """Summarize recorded durations without mutating business state."""
    log_path = run_logs_path(Path(state["run_root"]))
    log_text = _snapshot_text(_lexical_regular_file_snapshot(
        root=Path(state["report_root"]), relative=log_path.name, label="timing input log"
    ), label="timing input log")
    measurements: dict[str, dict[str, list]] = {}
    commands: dict[tuple[str, str], dict[str, Any]] = {}
    for line in log_text.splitlines():
        event = json.loads(line)
        if event.get("event") != "command-timing":
            continue
        record = event["details"]
        key = (event["phase"], record["command"])
        command = commands.setdefault(key, {"phase": key[0], "command": key[1], "calls": 0, "elapsed_seconds": 0.0})
        command["calls"] += 1
        command["elapsed_seconds"] = round(command["elapsed_seconds"] + record["elapsed_seconds"], 6)
        if record.get("attempt_id") and record.get("stage"):
            measurements.setdefault(record["attempt_id"], {}).setdefault(record["stage"], []).append({
                "started_at": record["started_at"], "finished_at": event["at"],
                "elapsed_seconds": record["elapsed_seconds"],
            })
    entries = [
        _timing_entry(attempt, measurements.get(identifier, {}))
        for identifier, attempt in state["attempts"].items()
    ]
    paused = (state.get("run_control") or {}).get("status") == "paused"
    run = {
        "status": "completed" if state["phase"] == "done" else "paused" if paused else "running",
        "phase": state["phase"], "created_at": state["created_at"],
    }
    if state.get("finished_at"):
        run.update(finished_at=state["finished_at"],
                   elapsed_seconds=_elapsed_between(state["created_at"], state["finished_at"]))
    write_json(_timing_path(Path(state["report_root"])), {
        "run": run,
        "commands": list(commands.values()),
        "annotation_attempts": [entry for entry in entries if entry["phase"] == "annotation"],
        "rounds": [entry for entry in entries if entry["phase"] != "annotation"],
    })

def _record_timing(run_root: Path, command: str, *, started_at: str, elapsed_seconds: float,
                   round_id: str | None = None, attempt_id: str | None = None,
                   exit_code: int | None = None) -> None:
    state = _load_state(run_root)
    identifier = (attempt_id or round_id or "").split(":", 1)[0]
    task = state["attempts"].get(identifier)
    _append_log(run_root, {
        "at": _utc(), "phase": task["phase"] if task else state["phase"], "event": "command-timing",
        "details": {"command": command, "attempt_id": identifier or None, "stage": command,
                    "started_at": started_at, "elapsed_seconds": elapsed_seconds, "exit_code": exit_code},
    })
    _write_timing_summary(state)

def _resolve_formal_case_lib_policy(
    args: argparse.Namespace, *, formal_case_lib: Path
) -> str:
    requested = getattr(args, "formal_case_lib_policy", None)
    policy = str(requested) if requested is not None else (
        "present" if formal_case_lib.is_file() else "create"
    )
    exists = os.path.lexists(formal_case_lib)
    if policy == "present" and not formal_case_lib.is_file():
        raise SystemExit(
            "--formal-case-lib-policy present requires the canonical lib file: "
            f"{formal_case_lib}"
        )
    if policy == "create" and exists:
        raise SystemExit(
            "--formal-case-lib-policy create requires an absent canonical path: "
            f"{formal_case_lib}"
        )
    if policy == "absent" and exists:
        raise SystemExit(
            "--formal-case-lib-policy absent requires the canonical path to be absent: "
            f"{formal_case_lib}"
        )
    return policy

def _create_formal_case_lib_seed(path: Path) -> None:
    """Create the canonical editable seed exactly once without following links."""

    path.parent.mkdir(parents=True, exist_ok=True)
    payload = FORMAL_CASE_LIB_SEED.encode("utf-8")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    for name in ("O_BINARY", "O_CLOEXEC", "O_NOFOLLOW"):
        flags |= int(getattr(os, name, 0) or 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError as exc:
        raise SystemExit(f"formal_case_lib seed target already exists: {path}") from exc
    try:
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)

def init_run(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    if (
        args.timestamp is not None
        and re.fullmatch(r"\d{14}", str(args.timestamp)) is None
    ):
        raise SystemExit("--timestamp must contain exactly 14 digits (YYYYMMDDhhmmss)")
    if args.max_witnesses_per_group < 1:
        raise SystemExit("--max-witnesses-per-group must be positive")
    if args.max_parallel_group_workers < 1:
        raise SystemExit("--max-parallel-group-workers must be positive")
    formal_case_name = str(args.case)
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", formal_case_name) is None:
        raise SystemExit(
            "--case must be a legal Rocq identifier because it is the "
            "authoritative formal artifact/module stem"
        )
    target = Path(args.target_c_file).expanduser()
    if not target.is_absolute():
        target = main_root / target
    target = fixed_path_under(target, main_root, label="target C file")
    qcp_examples_root = main_root / "QCP_examples"
    if (
        qcp_examples_root.resolve() != qcp_examples_root.absolute()
        or not target.is_file()
        or not target.is_relative_to(qcp_examples_root)
    ):
        raise SystemExit(
            f"target C file must exist under main-root/QCP_examples: {target}"
        )
    target_rel = target.relative_to(main_root).as_posix()
    try:
        target_files = target_files_for_c(
            target_rel,
            formal_case_name=formal_case_name,
        )
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    run_timestamp = args.timestamp or datetime.now().strftime("%Y%m%d%H%M%S")
    if os.name == "nt" and not _windows_long_paths_enabled():
        path_error = _windows_path_length_error(
            main_root=main_root,
            projected_run_name=(
                f"{slug(formal_case_name)}-{run_timestamp}-99"
            ),
            target_files=target_files,
        )
        if path_error:
            raise SystemExit(path_error)
    for key in (
        "formal_case_lib",
        "goal_file",
        "proof_auto_file",
        "proof_manual_file",
        "goal_check_file",
    ):
        relative = str(target_files[key])
        lexical = fixed_path_under(main_root / relative, main_root, label="formal target")
        if lexical.exists() and not lexical.is_file():
            raise SystemExit(f"formal target path is not a regular file: {relative}")
    formal_case_lib_path = main_root / str(target_files["formal_case_lib"])
    formal_case_lib_policy = _resolve_formal_case_lib_policy(
        args,
        formal_case_lib=formal_case_lib_path,
    )
    problem_context = _problem_context_from_args(args)
    spec_freeze = _spec_freeze_baseline(
        main_root=main_root,
        target_files=target_files,
        functions=_freeze_spec_functions(args),
    )
    if spec_freeze is not None and formal_case_lib_policy == "create":
        spec_freeze["baseline"]["lib"] = extract_lib(FORMAL_CASE_LIB_SEED)
    profile = symexec_profile_record(getattr(args, "symexec_profile", None))
    if detect_build_mode(main_root) == "dune":
        from coq_tooling_dune import clean_legacy_source_side_products

        cleanup = clean_legacy_source_side_products(main_root)
        if cleanup["status"] != "passed":
            raise SystemExit(f"Dune source artifact cleanup failed: {cleanup.get('first_error')}")
    run_root = ensure_run_root(main_root, args.case, timestamp=run_timestamp)
    report_root = reports_root(run_root)
    run_id = run_root.name
    if formal_case_lib_policy == "create":
        _create_formal_case_lib_seed(formal_case_lib_path)
    state: dict[str, Any] = {
        "schema_version": CONTROLLER_STATE_SCHEMA_VERSION,
        "generation": 0,
        "run_id": run_id,
        "case": args.case,
        "phase": "intake",
        "main_root": str(main_root),
        "run_root": str(run_root),
        "report_root": str(report_root),
        "target_files": target_files,
        "problem_context": problem_context,
        "formal_case_lib_policy": formal_case_lib_policy,
        "spec_freeze": spec_freeze,
        "run_control": {
            "status": "active",
            "pause_count": 0,
            "updated_at": _utc(),
        },
        "symexec_profile": profile,
        "max_witnesses_per_group": args.max_witnesses_per_group,
        "max_parallel_group_workers": args.max_parallel_group_workers,
        "dune_preparation": None,
        "attempts": {},
        "current": {phase: None for phase in TASK_PHASES},
        "annotation_owner": None,
        "pending_retry": None,
        "current_blockers": [],
        "final_candidate": None,
        "final_apply": None,
        "final_check": None,
        "created_at": _utc(),
    }
    from controller_control import _write_control_signal

    _write_control_signal(state)
    _append_event(
        run_root,
        state,
        "run-initialized",
        run_id=run_id,
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "run_id": run_id,
                "run_root": str(run_root),
                "report_root": str(report_root),
                "controller_state": str(controller_state_path(run_root)),
            },
            indent=2,
        )
    )
    return 0
