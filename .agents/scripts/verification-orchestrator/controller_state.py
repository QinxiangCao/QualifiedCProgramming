#!/usr/bin/env python3
"""Run creation, durable controller state, versions, logs, and snapshots.

This module is internal to controller.py.  It owns the controller's durable
state primitives; callers outside the controller use the controller CLI.
"""

# ruff: noqa: E402 -- controller modules resolve the internal vc-proving directory at runtime.

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parent / "vc-proving"
if str(VC_PROVING_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from file_integrity import sha256_file, sha256_text
from path_utils import (
    ANNOTATION_ATTEMPTS_DIR_NAME,
    ANNOTATION_HISTORY_DIR_NAME,
    TARGET_FILE_FIELDS,
    annotation_attempt_directory_name,
    controller_state_path,
    ensure_run_root,
    fixed_path_under,
    is_run_root_name,
    main_root_from_run_root,
    reports_root,
    reuse_source_build_workspace,
    reuse_source_preparation,
    run_logs_path,
    slug,
    target_files_for_c,
    write_json,
)
from coq_tooling import dune_snapshot_for_preserved_build
from proof_manual_utils import generated_artifact_module_spellings
from spec_freeze import extract_spec_surface
from public_helper_utils import (
    ensure_public_helper_lemma_lib,
    public_helper_pool_snapshot,
)
from symexec_tooling import _lexical_regular_file_snapshot, source_goal_version_at_root

GENERATED_KEYS = (
    "goal_file",
    "proof_auto_file",
    "proof_manual_file",
    "goal_check_file",
)
TARGET_TOPOLOGY_FILE_NAME = "controller_target_topology.json"
WINDOWS_LEGACY_DIRECTORY_PATH_LIMIT = 248
WINDOWS_LEGACY_FILE_PATH_LIMIT = 260
CONTROLLER_STATE_REQUIRED_FIELDS = frozenset(
    {
        "generation",
        "run_id",
        "case",
        "phase",
        "main_root",
        "run_root",
        "report_root",
        "target_files",
        "public_helper_lemma_lib",
        "problem_context",
        "spec_freeze",
        "max_compact_attempts",
        "max_witnesses_per_group",
        "max_parallel_group_workers",
        "source_version",
        "source_goal_version",
        "dune_preparation",
        "rounds",
        "attempts",
        "annotation_session",
        "accepted_rounds",
        "next_actions",
        "waiting_for",
        "current_blockers",
        "final_candidate",
        "final_apply",
        "final_check",
        "created_at",
        "updated_at",
    }
)
CONTROLLER_STATE_OPTIONAL_FIELDS = frozenset(
    {
        "finished_at",
        "final_apply_transaction",
        "public_helper_promotion_transaction",
    }
)


_STATE_METADATA: dict[int, dict[str, Any]] = {}
_PENDING_EVENTS: dict[int, list[dict[str, Any]]] = {}


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
    proving_round = f"{case_name}-vc-proving-r1"
    checking_round = f"{case_name}-vc-checking-r1"
    candidates = {
        "formal target": main_root / longest_formal,
        "annotation history": (
            run_root
            / ANNOTATION_HISTORY_DIR_NAME
            / annotation_attempt_directory_name(1)
            / "after"
            / longest_formal
        ),
        "vc-checking build": (
            run_root
            / "_coq_builds"
            / checking_round
            / "src"
            / longest_formal
        ),
        "group development build": (
            run_root
            / "_coq_builds"
            / proving_round
            / "group_9999"
            / "dev"
            / longest_formal
        ),
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
        "final backup": (
            report_root
            / "final-check"
            / "backup"
            / ("0" * 32)
            / longest_formal
        ),
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
        "Enable LongPathsEnabled and restart the process, or use a shorter "
        "main-root/case name; do not use subst, junctions, or aliases."
    )


@contextmanager
def _state_transaction(run_root: Path) -> Iterator[None]:
    """Validate the run boundary around one state mutation.

    Runs are intentionally single-controller.  Durability comes from atomic
    replacement plus generation checking; no filesystem synchronization
    primitive or marker file is created.
    """

    main_root = main_root_from_run_root(run_root)
    fixed_path_under(run_root, main_root, label="run root")
    yield


def _state_content_digest(state: dict[str, Any]) -> str:
    payload = {
        key: value
        for key, value in state.items()
        if key not in {"generation", "updated_at"}
    }
    return sha256_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":"))
    )


def _register_loaded_state(state: dict[str, Any]) -> None:
    _STATE_METADATA[id(state)] = {
        "state": state,
        "generation": int(state.get("generation", 0)),
        "content_digest": _state_content_digest(state),
    }


def _json_load(path: Path, default: Any | None = None) -> Any:
    if not path.is_file():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


_file_digest = sha256_file


def _debug_build_snapshot(
    build_workspace: Path,
    *,
    dune_dependency_snapshot: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Seal a preserved current build and its selected dependency snapshot.

    The keyword and digest member names retain ``dune_dependency`` for state
    compatibility; the value may describe either selected backend.
    """

    root = build_workspace.expanduser().resolve()
    if not root.is_dir():
        raise ValueError(f"debug build workspace is missing: {root}")
    records: list[dict[str, str]] = []
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root)
        if ".coq_debug" in relative.parts:
            continue
        records.append(
            {
                "relative_path": relative.as_posix(),
                "sha256": _file_digest(path),
            }
        )
    if not records:
        raise ValueError(f"debug build workspace has no preserved files: {root}")
    local_digest = sha256_text(
        json.dumps(records, sort_keys=True, separators=(",", ":"))
    )
    digest = local_digest
    if dune_dependency_snapshot is not None:
        base_digest = dune_dependency_snapshot.get("digest")
        base_file_count = dune_dependency_snapshot.get("file_count")
        if not isinstance(base_digest, str) or not base_digest:
            raise ValueError("selected dependency snapshot lacks a digest")
        if not isinstance(base_file_count, int) or base_file_count < 0:
            raise ValueError(
                "selected dependency snapshot has an invalid file count"
            )
        digest = sha256_text(
            json.dumps(
                {
                    "build_digest": local_digest,
                    "build_file_count": len(records),
                    "dune_dependency_digest": base_digest,
                    "dune_dependency_file_count": base_file_count,
                },
                sort_keys=True,
                separators=(",", ":"),
            )
        )
    return {"digest": digest, "file_count": len(records)}


def _verified_reuse_source_build(
    *,
    main_root: Path,
    run_root: Path,
    round_id: str,
    sealed: dict[str, Any],
    source_goal_version: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Re-verify one sealed reuse-source build against the preparation it carries.

    Raises ``ValueError`` when the preserved sources, that preparation, or the
    seal binding the two no longer agree.
    """

    if sealed.get("status") != "passed":
        raise ValueError(f"reuse-source build is not sealed: {round_id}")
    if sealed.get("source_goal_version") != source_goal_version:
        raise ValueError(
            f"sealed reuse-source build is bound to another goal version: {round_id}"
        )
    preparation_path = reuse_source_preparation(run_root, round_id)
    receipt = _json_load(preparation_path)
    if not isinstance(receipt, dict):
        raise ValueError(
            f"sealed reuse-source preparation is missing: {preparation_path}"
        )
    if sealed.get("preparation_sha256") != _file_digest(preparation_path):
        raise ValueError(
            f"sealed reuse-source preparation changed: {preparation_path}"
        )
    dependency_snapshot = dune_snapshot_for_preserved_build(
        workspace_root=main_root, receipt=receipt
    )
    build = _debug_build_snapshot(
        reuse_source_build_workspace(run_root, round_id),
        dune_dependency_snapshot=dependency_snapshot,
    )
    if (
        sealed.get("digest") != build["digest"]
        or sealed.get("file_count") != build["file_count"]
    ):
        raise ValueError(
            f"sealed reuse-source build changed after vc-proving preparation: {round_id}"
        )
    return dependency_snapshot["_snapshot"], build


def _is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.expanduser().resolve().relative_to(root.expanduser().resolve())
        return True
    except ValueError:
        return False


def _relative_path(path: Path, root: Path) -> str:
    return (
        path.expanduser().resolve().relative_to(root.expanduser().resolve()).as_posix()
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
    return {
        "functions": sorted(set(functions)),
        "baseline": extract_spec_surface(c_file, lib_file),
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


def _source_version(
    paths: list[Path],
    *,
    main_root: Path,
    roles: dict[str, str] | None = None,
) -> dict[str, Any]:
    owner_input = Path(os.path.abspath(os.fspath(main_root.expanduser())))
    try:
        owner = fixed_path_under(
            owner_input,
            owner_input,
            label="source-version main root",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    files: list[dict[str, Any]] = []
    digest_input: list[dict[str, Any]] = []
    for path in paths:
        try:
            candidate = fixed_path_under(
                path,
                owner,
                label="source-version artifact",
            )
        except SystemExit as exc:
            raise ValueError(str(exc)) from exc
        relative = candidate.relative_to(owner).as_posix()
        snapshot = _lexical_regular_file_snapshot(
            root=owner,
            relative=relative,
            label="source-version artifact",
        )
        if snapshot.get("state") == "missing":
            artifact_state = "missing"
            digest = None
        elif snapshot.get("state") != "present":
            detail = str(snapshot.get("message") or "invalid source topology")
            raise ValueError(
                "source-version artifact must be a non-link regular file or "
                f"truly absent: {relative}: {detail}"
            )
        else:
            artifact_state = "present"
            digest = str(snapshot["sha256"])
        entry: dict[str, Any] = {
            "relative_path": relative,
            "sha256": digest,
            "state": artifact_state,
        }
        role = (roles or {}).get(relative)
        if role:
            entry["role"] = role
        files.append(entry)
        digest_entry = {key: entry[key] for key in ("relative_path", "sha256", "state")}
        if role:
            digest_entry["role"] = role
        digest_input.append(digest_entry)
    digest_input.sort(
        key=lambda item: (str(item["relative_path"]), str(item.get("role", "")))
    )
    digest = sha256_text(
        json.dumps(digest_input, sort_keys=True, separators=(",", ":"))
    )
    return {
        "digest": digest,
        "files": files,
    }


def _source_version_for_state(
    state: dict[str, Any], *, annotated: bool
) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    target = state["target_files"]
    roles = {
        target["c_file"]: "target-c-annotated" if annotated else "target-c",
        target["formal_case_lib"]: "formal-case-lib",
    }
    return _source_version(
        [main_root / target["c_file"], main_root / target["formal_case_lib"]],
        main_root=main_root,
        roles=roles,
    )


def _formal_case_lib_is_active(state: dict[str, Any]) -> bool:
    """Return the run topology's persisted editable-lib presence."""

    relative = str(state["target_files"]["formal_case_lib"])
    source_version = state.get("source_version")
    records = source_version.get("files") if isinstance(source_version, dict) else None
    matches = (
        [
            record
            for record in records
            if isinstance(record, dict)
            and str(record.get("relative_path") or "") == relative
        ]
        if isinstance(records, list)
        else []
    )
    if len(matches) != 1:
        raise ValueError(
            "source_version requires exactly one formal_case_lib topology record"
        )
    record = matches[0]
    artifact_state = record.get("state")
    digest = record.get("sha256")
    if (
        artifact_state not in {"present", "missing"}
        or (artifact_state == "missing" and digest is not None)
        or (
            artifact_state == "present"
            and (
                not isinstance(digest, str)
                or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            )
        )
    ):
        raise ValueError("source_version formal_case_lib topology record is invalid")
    return artifact_state == "present"


def _formal_case_lib_snapshot(state: dict[str, Any]) -> dict[str, Any]:
    """Snapshot the exact optional case-lib leaf without following links."""

    return _lexical_regular_file_snapshot(
        root=Path(str(state["main_root"])),
        relative=str(state["target_files"]["formal_case_lib"]),
        label="formal_case_lib candidate",
    )


def _lexical_absolute_recorded_path(value: Any, *, label: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label} is missing or invalid")
    recorded = Path(value).expanduser()
    normalized = Path(os.path.abspath(os.fspath(recorded)))
    if not recorded.is_absolute() or recorded != normalized:
        raise ValueError(f"{label} must be an absolute normalized path")
    return normalized


def _exact_recorded_path(
    value: Any,
    expected: Path,
    *,
    owner: Path,
    label: str,
) -> Path:
    recorded = _lexical_absolute_recorded_path(value, label=label)
    if recorded != expected:
        raise ValueError(f"{label} differs from its fixed controller path")
    try:
        return fixed_path_under(recorded, owner, label=label)
    except (OSError, SystemExit) as exc:
        raise ValueError(str(exc)) from exc


def _validated_attempt_roots(
    state: dict[str, Any],
) -> tuple[Path, Path, Path]:
    """Return the exact current main/run/report roots without following aliases."""

    main_root = _lexical_absolute_recorded_path(
        state.get("main_root"), label="main root"
    )
    run_root = _lexical_absolute_recorded_path(
        state.get("run_root"), label="run root"
    )
    try:
        main_root = fixed_path_under(main_root, main_root, label="main root")
        run_root = fixed_path_under(run_root, main_root, label="run root")
    except (OSError, SystemExit) as exc:
        raise ValueError(str(exc)) from exc
    if run_root.parent != main_root / "verification_runs":
        raise ValueError("run root differs from its fixed controller path")
    expected_report_root = main_root / "reports" / run_root.name
    report_root = _exact_recorded_path(
        state.get("report_root"),
        expected_report_root,
        owner=main_root,
        label="run report root",
    )
    return main_root, run_root, report_root


def _validated_attempt_identity(
    state: dict[str, Any],
    attempt: dict[str, Any],
    *,
    proving: bool,
    allow_unregistered_attempt: bool = False,
) -> tuple[str, str, str]:
    attempt_id = attempt.get("attempt_id")
    round_id = attempt.get("round")
    phase = attempt.get("phase")
    if (
        not isinstance(attempt_id, str)
        or not attempt_id
        or not isinstance(round_id, str)
        or not round_id
        or Path(round_id).name != round_id
        or Path(round_id).is_absolute()
        or not isinstance(phase, str)
        or not phase
    ):
        raise ValueError("attempt identity contract is invalid")
    if proving:
        if attempt_id != round_id or phase != "vc-proving-preparing":
            raise ValueError("vc-proving attempt identity contract is invalid")
        round_phase = "vc-proving"
    else:
        compact_index = attempt.get("compact_attempt_index")
        if (
            isinstance(compact_index, bool)
            or not isinstance(compact_index, int)
            or compact_index < 1
            or attempt_id != f"{round_id}-attempt-{compact_index}"
        ):
            raise ValueError("phase attempt identity contract is invalid")
        round_phase = phase
    case_name = state.get("case")
    if (
        not isinstance(case_name, str)
        or re.fullmatch(
            rf"{re.escape(case_name)}-{re.escape(round_phase)}-r[1-9][0-9]*",
            round_id,
        )
        is None
    ):
        raise ValueError("attempt round identity differs from its phase and case")
    if not allow_unregistered_attempt:
        round_state = state.get("rounds", {}).get(round_id)
        if (
            not isinstance(round_state, dict)
            or round_state.get("phase") != phase
            or round_state.get("current_attempt") != attempt_id
        ):
            raise ValueError("attempt is not bound to its current round record")
        if state.get("attempts", {}).get(attempt_id) is not attempt:
            raise ValueError("attempt is not stored under its exact attempt_id")
    return attempt_id, round_id, phase


def _validated_annotation_attempt_paths(
    state: dict[str, Any],
    attempt: dict[str, Any],
    *,
    allow_missing_history: bool = False,
    allow_unregistered_attempt: bool = False,
) -> dict[str, Path]:
    """Bind every annotation attempt path to its controller-owned topology."""

    if attempt.get("phase") != "annotation":
        raise ValueError("annotation path validation requires an annotation attempt")
    attempt_id, round_id, _phase = _validated_attempt_identity(
        state,
        attempt,
        proving=False,
        allow_unregistered_attempt=allow_unregistered_attempt,
    )
    case_name = state.get("case")
    if (
        not isinstance(case_name, str)
        or not case_name
        or Path(round_id).name != round_id
        or Path(attempt_id).name != attempt_id
        or re.fullmatch(
            rf"{re.escape(case_name)}-annotation-r[1-9][0-9]*",
            round_id,
        )
        is None
    ):
        raise ValueError("annotation round path identity is invalid")
    annotation_iteration = attempt.get("annotation_iteration")
    if (
        isinstance(annotation_iteration, bool)
        or not isinstance(annotation_iteration, int)
        or annotation_iteration < 1
    ):
        raise ValueError("annotation iteration identity is invalid")
    causal_retry_count = attempt.get("annotation_causal_retry_count", 0)
    if (
        isinstance(causal_retry_count, bool)
        or not isinstance(causal_retry_count, int)
        or causal_retry_count < 0
    ):
        raise ValueError("annotation causal retry count is invalid")

    _main_root, run_root, report_root = _validated_attempt_roots(state)
    compact_name = annotation_attempt_directory_name(annotation_iteration)
    expected_report_directory = (
        report_root / ANNOTATION_ATTEMPTS_DIR_NAME / compact_name
    )
    report_directory = _exact_recorded_path(
        attempt.get("report_directory"),
        expected_report_directory,
        owner=report_root,
        label="annotation attempt report directory",
    )
    if not os.path.lexists(report_directory) or not report_directory.is_dir():
        raise ValueError(
            "annotation attempt report directory is missing or not a fixed directory"
        )

    compact_history = run_root / ANNOTATION_HISTORY_DIR_NAME / compact_name
    legacy_history = run_root / ANNOTATION_HISTORY_DIR_NAME / attempt_id
    expected_history = (
        legacy_history
        if Path(str(attempt.get("annotation_history_directory") or ""))
        == legacy_history
        else compact_history
    )
    history = _exact_recorded_path(
        attempt.get("annotation_history_directory"),
        expected_history,
        owner=run_root,
        label="annotation attempt history directory",
    )
    if os.path.lexists(history):
        if not history.is_dir():
            raise ValueError(
                "annotation attempt history path is not a fixed directory"
            )
    elif not allow_missing_history:
        raise ValueError("annotation attempt history directory is missing")

    paths: dict[str, Path] = {
        "directory": report_directory,
        "history": history,
        "before": history / "before",
        "after": history / "after",
    }
    filenames = {
        "input": "agent_input.md",
        "report": "agent_report.json",
        "output": "agent_output.md",
    }
    for field, filename in filenames.items():
        expected = report_directory / filename
        paths[field] = _exact_recorded_path(
            attempt.get(field),
            expected,
            owner=report_directory,
            label=f"annotation attempt {field}",
        )
        snapshot = _lexical_regular_file_snapshot(
            root=report_directory,
            relative=filename,
            label=f"annotation attempt {field}",
        )
        artifact_state = snapshot.get("state")
        if artifact_state == "missing" and field == "output":
            continue
        if artifact_state != "present":
            detail = str(snapshot.get("message") or "artifact is missing")
            raise ValueError(
                f"annotation attempt {field} is not a readable non-link regular "
                f"file: {detail}"
            )
    return paths


def _validated_phase_attempt_paths(
    state: dict[str, Any], attempt: dict[str, Any]
) -> dict[str, Path]:
    """Bind a non-annotation phase attempt to its current round report tree."""

    _attempt_id, round_id, phase = _validated_attempt_identity(
        state, attempt, proving=False
    )
    if phase != "vc-checking":
        raise ValueError("unsupported non-annotation phase attempt")
    _main_root, _run_root, report_root = _validated_attempt_roots(state)
    expected_directory = report_root / "rounds" / round_id
    directory = _exact_recorded_path(
        attempt.get("report_directory"),
        expected_directory,
        owner=report_root,
        label=f"{phase} attempt report directory",
    )
    if not os.path.lexists(directory) or not directory.is_dir():
        raise ValueError(
            f"{phase} attempt report directory is missing or not a fixed directory"
        )
    paths: dict[str, Path] = {
        "directory": directory,
        "reuse_hints": directory / "reuse_hints",
        "group_plan": directory / "group_plan.json",
    }
    for field, filename in (
        ("input", "agent_input.md"),
        ("report", "agent_report.json"),
        ("output", "agent_output.md"),
    ):
        paths[field] = _exact_recorded_path(
            attempt.get(field),
            directory / filename,
            owner=directory,
            label=f"{phase} attempt {field}",
        )
    if "group_plan" in attempt:
        _exact_recorded_path(
            attempt.get("group_plan"),
            paths["group_plan"],
            owner=directory,
            label=f"{phase} attempt group_plan",
        )
    if "reuse_hints" in attempt:
        _exact_recorded_path(
            attempt.get("reuse_hints"),
            paths["reuse_hints"],
            owner=directory,
            label=f"{phase} attempt reuse_hints",
        )
    return paths


def _validated_proving_attempt_paths(
    state: dict[str, Any], attempt: dict[str, Any]
) -> dict[str, Path]:
    """Bind every persisted vc-proving path to the current run and round."""

    _attempt_id, round_id, _phase = _validated_attempt_identity(
        state, attempt, proving=True
    )
    _main_root, run_root, report_root = _validated_attempt_roots(state)
    expected_directory = run_root / round_id
    expected_report_directory = report_root / "rounds" / slug(round_id)
    directory = _exact_recorded_path(
        attempt.get("directory"),
        expected_directory,
        owner=run_root,
        label="vc-proving attempt directory",
    )
    report_directory = _exact_recorded_path(
        attempt.get("report_directory"),
        expected_report_directory,
        owner=report_root,
        label="vc-proving attempt report directory",
    )
    for label, path in (
        ("vc-proving attempt directory", directory),
        ("vc-proving attempt report directory", report_directory),
    ):
        if not os.path.lexists(path) or not path.is_dir():
            raise ValueError(f"{label} is missing or not a fixed directory")
    return {
        "directory": directory,
        "report_directory": report_directory,
        "base_manifest": _exact_recorded_path(
            attempt.get("base_manifest"),
            directory / "base_manifest.json",
            owner=directory,
            label="vc-proving base_manifest",
        ),
        "group_workers_manifest": _exact_recorded_path(
            attempt.get("group_workers_manifest"),
            report_directory / "group_workers_manifest.json",
            owner=report_directory,
            label="vc-proving group_workers_manifest",
        ),
        "proving_merged_result": _exact_recorded_path(
            attempt.get("proving_merged_result"),
            report_directory / "proving_merged_result.json",
            owner=report_directory,
            label="vc-proving proving_merged_result",
        ),
    }


def _validated_attempt_paths(
    state: dict[str, Any],
    attempt: dict[str, Any],
    *,
    allow_missing_annotation_history: bool = False,
) -> dict[str, Path]:
    """Dispatch the exact topology check for one persisted attempt."""

    phase = attempt.get("phase")
    if phase == "annotation":
        return _validated_annotation_attempt_paths(
            state,
            attempt,
            allow_missing_history=allow_missing_annotation_history,
        )
    if phase == "vc-proving-preparing":
        return _validated_proving_attempt_paths(state, attempt)
    return _validated_phase_attempt_paths(state, attempt)


def _validate_accepted_round_path_topology(state: dict[str, Any]) -> None:
    accepted_rounds = state.get("accepted_rounds")
    if not isinstance(accepted_rounds, dict):
        raise ValueError("accepted_rounds is missing or invalid")
    _main_root, _run_root, report_root = _validated_attempt_roots(state)

    accepted_vc = accepted_rounds.get("vc-checking")
    if isinstance(accepted_vc, dict):
        attempt_id = accepted_vc.get("attempt_id")
        if attempt_id is None:
            plan = _exact_recorded_path(
                accepted_vc.get("group_plan"),
                report_root / "group_plan.json",
                owner=report_root,
                label="empty accepted vc-checking group_plan",
            )
            if accepted_vc.get("round") is not None or "reuse_hints" in accepted_vc:
                raise ValueError("empty accepted vc-checking pointer is invalid")
            del plan
        else:
            attempt = state.get("attempts", {}).get(str(attempt_id))
            if not isinstance(attempt, dict) or attempt.get("phase") != "vc-checking":
                raise ValueError("accepted vc-checking attempt is missing")
            paths = _validated_phase_attempt_paths(state, attempt)
            if (
                accepted_vc.get("round") != attempt.get("round")
                or accepted_vc.get("attempt_id") != attempt.get("attempt_id")
            ):
                raise ValueError("accepted vc-checking pointer identity is invalid")
            _exact_recorded_path(
                accepted_vc.get("group_plan"),
                paths["group_plan"],
                owner=paths["directory"],
                label="accepted vc-checking group_plan",
            )
            reuse_hints = accepted_vc.get("reuse_hints")
            if reuse_hints is not None:
                if not isinstance(reuse_hints, dict):
                    raise ValueError("accepted vc-checking reuse_hints is invalid")
                for group_id, receipt in reuse_hints.items():
                    if (
                        not isinstance(group_id, str)
                        or re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", group_id)
                        is None
                        or not isinstance(receipt, dict)
                    ):
                        raise ValueError(
                            "accepted vc-checking reuse-hint receipt is invalid"
                        )
                    _exact_recorded_path(
                        receipt.get("path"),
                        paths["reuse_hints"] / f"{group_id}.md",
                        owner=paths["reuse_hints"],
                        label=f"accepted vc-checking reuse hint {group_id}",
                    )

    accepted_proving = accepted_rounds.get("vc-proving-preparing")
    if isinstance(accepted_proving, dict):
        attempt_id = accepted_proving.get("attempt_id")
        attempt = state.get("attempts", {}).get(str(attempt_id))
        if not isinstance(attempt, dict):
            raise ValueError("accepted vc-proving attempt is missing")
        paths = _validated_proving_attempt_paths(state, attempt)
        if (
            accepted_proving.get("round") != attempt.get("round")
            or accepted_proving.get("attempt_id") != attempt.get("attempt_id")
        ):
            raise ValueError("accepted vc-proving pointer identity is invalid")
        final_candidate = state.get("final_candidate")
        if isinstance(final_candidate, dict):
            if final_candidate.get("round") != attempt.get("round"):
                raise ValueError("final candidate round differs from accepted proving")
            _exact_recorded_path(
                final_candidate.get("proving_merged_result"),
                paths["proving_merged_result"],
                owner=paths["report_directory"],
                label="final candidate proving_merged_result",
            )


def _validate_controller_attempt_topologies(state: dict[str, Any]) -> None:
    attempts = state.get("attempts")
    rounds = state.get("rounds")
    if not isinstance(attempts, dict) or not isinstance(rounds, dict):
        raise ValueError("controller attempts or rounds are missing or invalid")
    for attempt_id, attempt in attempts.items():
        if not isinstance(attempt_id, str) or not isinstance(attempt, dict):
            raise ValueError("controller attempt record is invalid")
        if attempt.get("attempt_id") != attempt_id:
            raise ValueError("controller attempt map key differs from attempt_id")
        _validated_attempt_paths(state, attempt)
    for round_id, round_state in rounds.items():
        current_attempt = (
            attempts.get(round_state.get("current_attempt"))
            if isinstance(round_state, dict)
            else None
        )
        if (
            not isinstance(round_id, str)
            or Path(round_id).name != round_id
            or Path(round_id).is_absolute()
            or not isinstance(round_state, dict)
            or set(round_state) != {"phase", "current_attempt"}
            or not isinstance(current_attempt, dict)
            or current_attempt.get("round") != round_id
            or current_attempt.get("phase") != round_state.get("phase")
        ):
            raise ValueError("controller round record is invalid")
    _validate_accepted_round_path_topology(state)


def _generated_artifact_module_spellings_for_state(
    state: dict[str, Any],
    *,
    source_goal_version: dict[str, Any] | None = None,
) -> frozenset[str]:
    """Bind the exact generated-module import boundary to current topology.

    Before annotation acceptance, callers omit ``source_goal_version`` and the
    current filesystem determines which optional generated artifacts exist.
    Acceptance and later phases pass their just-computed or persisted version
    record so the boundary is sealed to the same presence topology as final
    checking.
    """

    target = state["target_files"]
    if source_goal_version is None:
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
    else:
        records = source_goal_version.get("generated_files")
        if not isinstance(records, list):
            raise ValueError("source_goal_version generated_files is invalid")
        present_roles: set[str] = set()
        for role in GENERATED_KEYS:
            matches = [
                record
                for record in records
                if isinstance(record, dict) and record.get("role") == role
            ]
            if len(matches) != 1:
                raise ValueError(
                    f"source_goal_version requires exactly one generated record for {role}"
                )
            record = matches[0]
            if (
                record.get("relative_path") != target[role]
                or record.get("state") not in {"present", "missing"}
            ):
                raise ValueError(
                    f"source_goal_version generated record is invalid for {role}"
                )
            if record["state"] == "present":
                present_roles.add(role)
    return generated_artifact_module_spellings(target, roles=present_roles)


def _source_goal_version(state: dict[str, Any]) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    return source_goal_version_at_root(
        root=main_root,
        target_files=state["target_files"],
    )


def _current_generated_records(state: dict[str, Any]) -> list[dict[str, Any]]:
    """Hash current generated bytes without reparsing unchanged obligations."""

    main_root = Path(str(state["main_root"]))
    owner_input = Path(os.path.abspath(os.fspath(main_root.expanduser())))
    try:
        owner = fixed_path_under(
            owner_input,
            owner_input,
            label="current generated main root",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    target = state["target_files"]
    records: list[dict[str, Any]] = []
    for role in GENERATED_KEYS:
        relative = str(target[role])
        try:
            fixed_path_under(
                owner / relative,
                owner,
                label=f"current generated {role}",
            )
        except SystemExit as exc:
            raise ValueError(str(exc)) from exc
        snapshot = _lexical_regular_file_snapshot(
            root=owner,
            relative=relative,
            label=f"current generated {role}",
        )
        if snapshot.get("state") == "missing":
            artifact_state = "missing"
            digest = None
        elif snapshot.get("state") != "present":
            detail = str(snapshot.get("message") or "invalid generated topology")
            raise ValueError(
                f"current generated {role} must be a non-link regular file or "
                f"truly absent: {relative}: {detail}"
            )
        else:
            artifact_state = "present"
            digest = str(snapshot["sha256"])
        records.append(
            {
                "relative_path": relative,
                "role": role,
                "state": artifact_state,
                "sha256": digest,
            }
        )
    return records


def _current_version_errors(state: dict[str, Any]) -> list[str]:
    """Compare current root inputs/goals with the accepted annotation versions."""

    errors: list[str] = []
    try:
        current_source = _source_version_for_state(state, annotated=True)
        current_generated = _current_generated_records(state)
    except (OSError, ValueError) as exc:
        return [f"current formal state cannot be versioned: {exc}"]
    saved_source_record = state.get("source_version") or {}
    saved_goal_record = state.get("source_goal_version") or {}
    saved_source = str(saved_source_record.get("digest") or "")
    saved_goal = str(saved_goal_record.get("digest") or "")
    if not saved_source or current_source["digest"] != saved_source:
        errors.append("current target C or formal_case_lib differs from source_version")
    if (
        not saved_goal
        or saved_goal_record.get("generated_files") != current_generated
    ):
        errors.append("current generated/manual files differ from source_goal_version")
    accepted = state.get("accepted_rounds", {}).get("annotation", {})
    if (
        accepted.get("source_version") != saved_source
        or accepted.get("source_goal_version") != saved_goal
    ):
        errors.append("accepted annotation versions do not match controller state")
    return errors


def _run_root_from_id(main_root: Path, run_id: str) -> Path:
    if Path(run_id).name != run_id or not is_run_root_name(run_id):
        raise SystemExit(f"invalid run id: {run_id}")
    owner = main_root.expanduser().resolve()
    path = fixed_path_under(
        owner / "verification_runs" / run_id,
        owner,
        label="run root",
    )
    if path.parent != owner / "verification_runs":
        raise SystemExit(f"run is outside the main root: {path}")
    if not path.is_dir():
        raise SystemExit(f"run not found: {path}")
    return path


def _validate_target_files_topology(
    state: dict[str, Any],
    *,
    main_root: Path,
) -> None:
    """Bind every persisted target field to C path + Rocq case identity."""

    case_name = state.get("case")
    target_files = state.get("target_files")
    if (
        not isinstance(case_name, str)
        or re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", case_name) is None
    ):
        raise SystemExit("controller state case is not a legal Rocq artifact stem")
    if (
        not isinstance(target_files, dict)
        or set(target_files) != TARGET_FILE_FIELDS
        or any(
            not isinstance(value, str) or not value
            for value in target_files.values()
        )
    ):
        raise SystemExit("controller state target_files has invalid fields")
    if target_files.get("case_name") != case_name:
        raise SystemExit("controller state case does not match target_files case_name")
    try:
        expected = target_files_for_c(
            target_files["c_file"],
            formal_case_name=case_name,
        )
    except ValueError as exc:
        raise SystemExit(f"controller state target_files is invalid: {exc}") from exc
    if target_files != expected:
        raise SystemExit(
            "controller state target_files does not match its canonical C/case topology"
        )
    for field in (
        "c_file",
        "formal_directory",
        "formal_case_lib",
        *GENERATED_KEYS,
    ):
        try:
            fixed_path_under(
                main_root / target_files[field],
                main_root,
                label=f"controller state target_files {field}",
            )
        except SystemExit as exc:
            raise SystemExit(
                f"controller state target_files {field} is not lexically confined: {exc}"
            ) from exc


def _target_topology_payload(state: dict[str, Any]) -> dict[str, Any]:
    return {
        "run_id": state["run_id"],
        "case": state["case"],
        "target_files": state["target_files"],
    }


def _write_target_topology_anchor(
    *,
    main_root: Path,
    report_root: Path,
    state: dict[str, Any],
) -> None:
    """Create the run's immutable identity anchor exactly once."""

    anchor = fixed_path_under(
        report_root / TARGET_TOPOLOGY_FILE_NAME,
        main_root,
        label="controller target topology anchor",
    )
    payload = (
        json.dumps(
            _target_topology_payload(state),
            indent=2,
            ensure_ascii=True,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    for name in ("O_BINARY", "O_CLOEXEC", "O_NOFOLLOW"):
        flags |= int(getattr(os, name, 0) or 0)
    try:
        descriptor = os.open(anchor, flags, 0o600)
    except FileExistsError as exc:
        raise SystemExit(
            f"controller target topology anchor already exists: {anchor}"
        ) from exc
    try:
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _validated_target_topology_anchor(
    *,
    report_root: Path,
    state: dict[str, Any],
) -> None:
    """Require the fixed non-link anchor to match the loaded state exactly."""

    snapshot = _lexical_regular_file_snapshot(
        root=report_root,
        relative=TARGET_TOPOLOGY_FILE_NAME,
        label="controller target topology anchor",
    )
    if snapshot.get("state") != "present":
        detail = str(snapshot.get("message") or snapshot.get("state") or "invalid")
        raise SystemExit(
            "controller target topology anchor is missing or invalid: " + detail
        )

    def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON field: {key}")
            result[key] = value
        return result

    try:
        anchor = json.loads(
            bytes(snapshot["data"]).decode("utf-8"),
            object_pairs_hook=strict_object,
        )
    except (UnicodeDecodeError, ValueError, TypeError) as exc:
        raise SystemExit(
            f"controller target topology anchor is not strict JSON: {exc}"
        ) from exc
    if not isinstance(anchor, dict) or anchor != _target_topology_payload(state):
        raise SystemExit(
            "controller target topology anchor does not match controller state"
        )


def _load_state(run_root: Path) -> dict[str, Any]:
    main_root = main_root_from_run_root(run_root)
    path = fixed_path_under(
        controller_state_path(run_root),
        main_root,
        label="controller state",
    )
    state = _json_load(path)
    if not isinstance(state, dict):
        raise SystemExit(f"controller state is missing or invalid: {path}")
    if (
        CONTROLLER_STATE_REQUIRED_FIELDS - set(state)
        or set(state)
        - CONTROLLER_STATE_REQUIRED_FIELDS
        - CONTROLLER_STATE_OPTIONAL_FIELDS
    ):
        raise SystemExit("controller state contains unsupported or missing fields")
    fixed_run_root = fixed_path_under(run_root, main_root, label="run root")
    recorded_run_root = fixed_path_under(
        Path(str(state.get("run_root", ""))),
        main_root,
        label="controller state run_root",
    )
    if recorded_run_root != fixed_run_root:
        raise SystemExit(
            "controller state run_root does not match its fixed run directory"
        )
    recorded_main_root = fixed_path_under(
        Path(str(state.get("main_root", ""))),
        main_root.parent,
        label="controller state main_root",
    )
    if recorded_main_root != main_root:
        raise SystemExit(
            "controller state main_root does not own its fixed run directory"
        )
    expected_report_root = reports_root(fixed_run_root)
    recorded_report_root = fixed_path_under(
        Path(str(state.get("report_root", ""))),
        main_root,
        label="controller state report_root",
    )
    if recorded_report_root != expected_report_root:
        raise SystemExit(
            "controller state report_root does not match its fixed report directory"
        )
    if not isinstance(state.get("generation"), int) or int(state["generation"]) < 1:
        raise SystemExit("controller state generation is missing or invalid")
    _validate_target_files_topology(state, main_root=main_root)
    run_id = state.get("run_id")
    case_name = str(state["case"])
    expected_run_id = rf"{re.escape(slug(case_name))}-\d{{14}}(?:-\d{{2}})?"
    if (
        not isinstance(run_id, str)
        or run_id != fixed_run_root.name
        or re.fullmatch(expected_run_id, run_id) is None
    ):
        raise SystemExit(
            "controller state run_id does not match its case and fixed run directory"
        )
    _validated_target_topology_anchor(
        report_root=expected_report_root,
        state=state,
    )
    try:
        _validate_controller_attempt_topologies(state)
    except (OSError, ValueError) as exc:
        raise SystemExit(
            f"controller state attempt path topology is invalid: {exc}"
        ) from exc
    _register_loaded_state(state)
    return state


def _append_log(run_root: Path, record: dict[str, Any]) -> None:
    path = fixed_path_under(
        run_logs_path(run_root),
        main_root_from_run_root(run_root),
        label="controller run log",
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True, ensure_ascii=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def _append_event(
    run_root: Path, state: dict[str, Any], event: str, **details: Any
) -> None:
    del run_root
    _PENDING_EVENTS.setdefault(id(state), []).append(
        {
            "at": _utc(),
            "event": event,
            "phase": state.get("phase"),
            "details": details,
        }
    )


def _save_state(run_root: Path, state: dict[str, Any]) -> None:
    """Commit one state mutation with generation-CAS and post-commit event logging."""

    root = fixed_path_under(
        run_root,
        main_root_from_run_root(run_root),
        label="run root",
    )
    with _state_transaction(root):
        try:
            path = controller_state_path(root)
            current = _json_load(path)
            candidate_metadata = _STATE_METADATA.get(id(state))
            metadata = (
                candidate_metadata
                if isinstance(candidate_metadata, dict)
                and candidate_metadata.get("state") is state
                else None
            )
            if isinstance(current, dict):
                if (
                    set(current) - CONTROLLER_STATE_OPTIONAL_FIELDS
                    != set(state) - CONTROLLER_STATE_OPTIONAL_FIELDS
                ):
                    raise SystemExit(
                        "controller state fields changed before generation CAS"
                    )
                current_generation = int(current.get("generation", 0))
                expected_generation = (
                    int(metadata["generation"])
                    if isinstance(metadata, dict)
                    else int(state.get("generation", 0))
                )
                if current_generation != expected_generation:
                    base_digest = (
                        str(metadata.get("content_digest") or "")
                        if isinstance(metadata, dict)
                        else ""
                    )
                    if (
                        not base_digest
                        or _state_content_digest(current) != base_digest
                    ):
                        raise SystemExit(
                            "controller state changed during this command; refusing a stale whole-state write"
                        )
                state["generation"] = current_generation + 1
            else:
                state["generation"] = max(1, int(state.get("generation", 0)) + 1)
            try:
                _validate_controller_attempt_topologies(state)
            except (OSError, ValueError) as exc:
                raise SystemExit(
                    f"refusing to persist invalid attempt path topology: {exc}"
                ) from exc
            state["updated_at"] = _utc()
            write_json(path, state)
        except BaseException:
            _PENDING_EVENTS.pop(id(state), None)
            raise
        for record in _PENDING_EVENTS.pop(id(state), []):
            _append_log(root, record)
        _register_loaded_state(state)
        _write_timing_summary(state)


def _mutate_state[MutationResult](
    run_root: Path,
    mutation: Callable[[dict[str, Any]], MutationResult],
) -> MutationResult:
    """Load and commit one small run-scoped mutation."""

    root = run_root.expanduser().resolve()
    with _state_transaction(root):
        state = _load_state(root)
        result = mutation(state)
        _save_state(root, state)
        return result


def _record_attempt_elapsed(
    run_root: Path,
    *,
    attempt_id: str,
    stage: str,
    elapsed_seconds: float,
) -> None:
    """Append timing to a freshly loaded attempt instead of saving a stale check snapshot."""

    def record(state: dict[str, Any]) -> None:
        attempt = state.get("attempts", {}).get(attempt_id)
        if isinstance(attempt, dict):
            _record_elapsed_stage(attempt, stage, elapsed_seconds)

    _mutate_state(run_root, record)


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


def _timing_entry(attempt: dict[str, Any]) -> dict[str, Any]:
    phase = str(attempt.get("phase") or "")
    if phase == "annotation":
        identifier = f"annotation-attempt{int(attempt.get('annotation_iteration', 0))}"
        entry: dict[str, Any] = {"attempt": identifier, "round": attempt["round"]}
        lifecycle_name = "annotation-work"
    else:
        entry = {
            "round": attempt["round"],
            "phase": "vc-proving" if phase == "vc-proving-preparing" else phase,
        }
        lifecycle_name = "witness-analysis" if phase == "vc-checking" else "group-work"
    entry["status"] = attempt.get("status")
    created_at = str(attempt.get("created_at") or "")
    finished_at = str(attempt.get("finished_at") or "")
    if created_at:
        entry["created_at"] = created_at
    if finished_at:
        entry["finished_at"] = finished_at
        entry["elapsed_seconds"] = _elapsed_between(created_at, finished_at)

    stages: list[dict[str, Any]] = []
    if phase in {"annotation", "vc-checking"}:
        lifecycle = _lifecycle_stage(
            lifecycle_name,
            str(attempt.get("started_at") or "") or None,
            str(attempt.get("returned_at") or "") or None,
        )
    else:
        group_intervals = (attempt.get("timing") or {}).get("group-work", [])
        if group_intervals:
            starts = [
                str(item["started_at"])
                for item in group_intervals
                if item.get("started_at")
            ]
            ends = [
                str(item["finished_at"])
                for item in group_intervals
                if item.get("finished_at")
            ]
        else:
            groups = list((attempt.get("groups") or {}).values())
            starts = [
                str(group["started_at"]) for group in groups if group.get("started_at")
            ]
            ends = [
                str(group["returned_at"])
                for group in groups
                if group.get("returned_at")
            ]
        lifecycle = _lifecycle_stage(
            lifecycle_name,
            min(starts, key=_parse_utc) if starts else None,
            max(ends, key=_parse_utc) if starts and len(ends) == len(starts) else None,
        )
    if lifecycle is not None:
        stages.append(lifecycle)

    stage_order = {
        "annotation": (
            "symexec",
            "formal-case-lib-coq-check",
            "clean-output-freshness",
            "annotation-checking",
            "controller-validation",
            "controller-acceptance-check",
            "dune-build",
        ),
        "vc-checking": ("controller-validation", "controller-plan-check"),
        "vc-proving-preparing": (
            "preparing",
            "group-development-check",
            "group-coq-check",
            "group-validation",
            "parent-verify",
        ),
    }
    timing = attempt.get("timing") if isinstance(attempt.get("timing"), dict) else {}
    for name in stage_order.get(phase, ()):
        aggregate = _aggregate_stage(name, timing.get(name, []))
        if aggregate is not None:
            stages.append(aggregate)
    entry["stages"] = stages
    return entry


def _write_timing_summary(state: dict[str, Any]) -> None:
    attempts = list(state.get("attempts", {}).values())
    annotation = sorted(
        (_timing_entry(item) for item in attempts if item.get("phase") == "annotation"),
        key=lambda item: int(str(item["attempt"]).removeprefix("annotation-attempt")),
    )
    rounds = [
        _timing_entry(item)
        for item in attempts
        if item.get("phase") in {"vc-checking", "vc-proving-preparing"}
    ]
    rounds.sort(key=lambda item: str(item["created_at"]))
    created_at = str(state.get("created_at") or "")
    finished_at = str(state.get("finished_at") or "")
    run: dict[str, Any] = {
        "status": "completed" if state.get("phase") == "done" else "running",
        "phase": str(state.get("phase") or ""),
    }
    if created_at:
        run["created_at"] = created_at
    if created_at and finished_at:
        run["finished_at"] = finished_at
        run["elapsed_seconds"] = _elapsed_between(created_at, finished_at)

    proving_finishes = [
        str(item.get("finished_at"))
        for item in attempts
        if item.get("phase") == "vc-proving-preparing"
        and item.get("status") == "verified"
        and item.get("finished_at")
    ]
    final_apply = (
        state.get("final_apply") if isinstance(state.get("final_apply"), dict) else {}
    )
    final_check = (
        state.get("final_check") if isinstance(state.get("final_check"), dict) else {}
    )
    finalization: dict[str, Any] = {
        "status": str(
            final_check.get("status") or final_apply.get("status") or "pending"
        )
    }
    final_started = max(proving_finishes, key=_parse_utc) if proving_finishes else ""
    final_finished = str(final_check.get("checked_at") or "")
    if final_started:
        finalization["started_at"] = final_started
    if final_apply.get("applied_at"):
        finalization["applied_at"] = str(final_apply["applied_at"])
    if final_started and final_finished:
        finalization["finished_at"] = final_finished
        finalization["elapsed_seconds"] = _elapsed_between(
            final_started, final_finished
        )
    write_json(
        _timing_path(Path(str(state["report_root"]))),
        {
            "run": run,
            "annotation_attempts": annotation,
            "rounds": rounds,
            "finalization": finalization,
        },
    )


def _record_timing(
    run_root: Path,
    command: str,
    *,
    started_at: str,
    elapsed_seconds: float,
    round_id: str | None = None,
    attempt_id: str | None = None,
) -> None:
    # Timing starts from freshly loaded state after the command so it cannot
    # write back a pre-check snapshot.
    with _state_transaction(run_root):
        state = _load_state(run_root)
        attempt: dict[str, Any] | None = None
        stage: str | None = None
        if command in {
            "annotation-check-round",
            "vc-checking-check-round",
            "vc-proving-preparing",
            "vc-proving-verify",
        }:
            round_state = state.get("rounds", {}).get(str(round_id), {})
            attempt = state.get("attempts", {}).get(
                str(round_state.get("current_attempt"))
            )
            stage = {
                "annotation-check-round": "controller-acceptance-check",
                "vc-checking-check-round": "controller-plan-check",
                "vc-proving-preparing": "preparing",
                "vc-proving-verify": "parent-verify",
            }[command]
        elif command == "dune-build":
            accepted_annotation = state.get("accepted_rounds", {}).get(
                "annotation", {}
            )
            attempt = state.get("attempts", {}).get(
                str(accepted_annotation.get("attempt_id") or "")
            )
            stage = "dune-build"
        elif command == "finalize-delivery" and attempt_id:
            if ":" in attempt_id:
                proving_round, _group = attempt_id.split(":", 1)
                attempt = state.get("attempts", {}).get(proving_round)
                stage = "group-validation"
            else:
                attempt = state.get("attempts", {}).get(attempt_id)
                stage = "controller-validation"
        if not isinstance(attempt, dict) or not stage:
            return
        finished_at = _utc()
        _record_timing_interval(
            attempt,
            stage,
            started_at=started_at,
            finished_at=finished_at,
            elapsed_seconds=elapsed_seconds,
        )
        if attempt.get("status") in {
            "accepted",
            "blocked",
            "stale",
            "superseded",
            "invalid-report",
            "main-check-failed",
            "parent-verify-failed",
            "verified",
        }:
            attempt["finished_at"] = finished_at
        _save_state(run_root, state)


def timing_stage(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    round_state = state.get("rounds", {}).get(args.round, {})
    attempt = state.get("attempts", {}).get(str(round_state.get("current_attempt")))
    if not isinstance(attempt, dict) or attempt.get("phase") != "annotation":
        raise SystemExit(f"annotation round not found for timing stage: {args.round}")
    if attempt.get("status") != "running" or not attempt.get("started_at"):
        raise SystemExit(
            "annotation attempt must be running before timing annotation-checking"
        )
    intervals = attempt.setdefault("timing", {}).setdefault(args.stage, [])
    if args.event == "start":
        if intervals and not intervals[-1].get("finished_at"):
            raise SystemExit(f"timing stage is already running: {args.stage}")
        _record_timing_interval(attempt, args.stage, started_at=_utc())
    else:
        if not intervals or intervals[-1].get("finished_at"):
            raise SystemExit(f"timing stage has no open interval: {args.stage}")
        finished_at = _utc()
        intervals[-1]["finished_at"] = finished_at
        intervals[-1]["elapsed_seconds"] = _elapsed_between(
            str(intervals[-1]["started_at"]), finished_at
        )
    _save_state(run_root, state)
    return 0


def _snapshot_files(state: dict[str, Any], destination: Path) -> None:
    main_root = Path(str(state["main_root"]))
    run_root = Path(str(state["run_root"]))
    try:
        destination = fixed_path_under(
            destination,
            run_root,
            label="annotation history snapshot destination",
        )
    except (SystemExit, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    if os.path.lexists(destination) and not destination.is_dir():
        raise SystemExit(
            f"annotation history snapshot destination is not a fixed directory: {destination}"
        )
    destination.mkdir(parents=True, exist_ok=True)
    for key in ("c_file", "formal_case_lib", *GENERATED_KEYS):
        relative = str(state["target_files"][key])
        snapshot = _lexical_regular_file_snapshot(
            root=main_root,
            relative=relative,
            label=f"annotation snapshot source {key}",
        )
        if snapshot.get("state") == "missing":
            continue
        if snapshot.get("state") != "present" or not isinstance(
            snapshot.get("data"), bytes
        ):
            detail = str(snapshot.get("message") or "invalid source topology")
            raise SystemExit(
                f"annotation snapshot source is not a readable non-link regular file: "
                f"{relative}: {detail}"
            )
        try:
            target = fixed_path_under(
                destination / relative,
                destination,
                label=f"annotation history snapshot target {key}",
            )
        except SystemExit as exc:
            raise SystemExit(str(exc)) from exc
        if os.path.lexists(target):
            raise SystemExit(
                f"annotation history snapshot target already exists: {relative}"
            )
        target.parent.mkdir(parents=True, exist_ok=True)
        try:
            fixed_path_under(
                target.parent,
                destination,
                label=f"annotation history snapshot target parent {key}",
            )
        except SystemExit as exc:
            raise SystemExit(str(exc)) from exc
        target.write_bytes(snapshot["data"])


def _annotation_snapshot_relatives(state: dict[str, Any]) -> list[str]:
    return [
        str(state["target_files"][key])
        for key in ("c_file", "formal_case_lib", *GENERATED_KEYS)
    ]


def _annotation_snapshot_record(
    state: dict[str, Any], snapshot_root: Path
) -> dict[str, Any]:
    try:
        root = fixed_path_under(
            snapshot_root,
            Path(str(state["run_root"])),
            label="annotation history snapshot root",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    if not os.path.lexists(root) or not root.is_dir():
        raise ValueError(
            f"annotation history snapshot is missing or not a fixed directory: {root}"
        )
    records: list[dict[str, Any]] = []
    for relative in _annotation_snapshot_relatives(state):
        snapshot = _lexical_regular_file_snapshot(
            root=root,
            relative=relative,
            label="annotation history snapshot artifact",
        )
        artifact_state = snapshot.get("state")
        if artifact_state not in {"present", "missing"}:
            detail = str(snapshot.get("message") or "invalid snapshot topology")
            raise ValueError(
                "annotation history snapshot path is not a readable non-link "
                f"regular file: {relative}: {detail}"
            )
        present = artifact_state == "present"
        records.append(
            {
                "relative_path": relative,
                "state": "present" if present else "missing",
                "sha256": str(snapshot["sha256"]) if present else None,
            }
        )
    return {
        "digest": sha256_text(
            json.dumps(records, sort_keys=True, separators=(",", ":"))
        ),
        "file_count": sum(record["state"] == "present" for record in records),
        "missing_count": sum(record["state"] == "missing" for record in records),
    }


def _snapshot_digests(root: Path, relatives: list[str]) -> dict[str, str | None]:
    version = _source_version(
        [root / relative for relative in relatives],
        main_root=root,
    )
    return {
        str(record["relative_path"]): (
            str(record["sha256"]) if record["state"] == "present" else None
        )
        for record in version["files"]
    }


def _archive_annotation_stage(
    state: dict[str, Any],
    attempt: dict[str, Any],
    stage: str,
    *,
    initializing: bool = False,
) -> dict[str, Any]:
    try:
        attempt_paths = _validated_annotation_attempt_paths(
            state,
            attempt,
            allow_missing_history=True,
            allow_unregistered_attempt=initializing,
        )
        history = attempt_paths["history"]
        destination = fixed_path_under(
            history / stage,
            history,
            label="annotation history stage",
        )
    except (SystemExit, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    if os.path.lexists(destination):
        if not destination.is_dir():
            raise SystemExit(
                f"annotation history stage is not a fixed directory: {destination}"
            )
        shutil.rmtree(destination)
    _snapshot_files(state, destination)
    try:
        return _annotation_snapshot_record(state, destination)
    except (OSError, ValueError) as exc:
        raise SystemExit(f"failed to seal annotation history {stage}: {exc}") from exc


def _annotation_before_snapshot_errors(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    expected = attempt.get("before_snapshot")
    if not isinstance(expected, dict):
        return ["annotation attempt has no sealed before-history snapshot"]
    try:
        attempt_paths = _validated_annotation_attempt_paths(state, attempt)
        before = attempt_paths["before"]
        current = _annotation_snapshot_record(state, before)
    except (OSError, ValueError) as exc:
        return [str(exc)]
    if current != expected:
        return ["annotation before-history snapshot changed after attempt creation"]
    return []


def _annotation_after_snapshot_errors(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    """Revalidate the immutable post-delivery annotation history seal."""

    expected = attempt.get("after_snapshot")
    if not isinstance(expected, dict):
        # The archived bytes are evidence only when finalize-delivery recorded
        # their digest.  Hashing an unsealed directory on first read would turn
        # its current, possibly modified contents into trusted provenance.
        return ["annotation attempt has no sealed after-history snapshot"]
    try:
        attempt_paths = _validated_annotation_attempt_paths(state, attempt)
        after = attempt_paths["after"]
        current = _annotation_snapshot_record(state, after)
    except (OSError, ValueError) as exc:
        return [str(exc)]
    if current != expected:
        return ["annotation after-history snapshot changed after finalize-delivery"]
    return []


def _annotation_changed_files(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    relatives = [
        str(state["target_files"][key])
        for key in ("c_file", "formal_case_lib", *GENERATED_KEYS)
    ]
    try:
        history = _validated_annotation_attempt_paths(state, attempt)["history"]
        before = _snapshot_digests(history / "before", relatives)
        after = _snapshot_digests(history / "after", relatives)
    except (OSError, ValueError):
        return relatives
    return [relative for relative in relatives if before[relative] != after[relative]]


def _annotation_current_changed_files(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    """Compare the archived before image with current root before sealing delivery."""

    main_root = Path(str(state["main_root"]))
    relatives = [
        str(state["target_files"][key])
        for key in ("c_file", "formal_case_lib", *GENERATED_KEYS)
    ]
    try:
        history = _validated_annotation_attempt_paths(state, attempt)["history"]
        before = _snapshot_digests(history / "before", relatives)
        current = _snapshot_digests(main_root, relatives)
    except (OSError, ValueError):
        return relatives
    return [relative for relative in relatives if before[relative] != current[relative]]


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
    if args.max_compact_attempts < 1:
        raise SystemExit("--max-compact-attempts must be positive")
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
    target = target.resolve()
    qcp_examples_root = main_root / "QCP_examples"
    if (
        qcp_examples_root.resolve() != qcp_examples_root.absolute()
        or not target.is_file()
        or not _is_relative_to(target, qcp_examples_root)
    ):
        raise SystemExit(
            f"target C file must exist under main-root/QCP_examples: {target}"
        )
    target_rel = _relative_path(target, main_root)
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
        lexical = main_root / relative
        if lexical.resolve() != lexical.absolute():
            raise SystemExit(
                f"formal target path uses a symlink or escapes main root: {relative}"
            )
        if lexical.exists() and not lexical.is_file():
            raise SystemExit(f"formal target path is not a regular file: {relative}")
    run_root = ensure_run_root(main_root, args.case, timestamp=run_timestamp)
    report_root = reports_root(run_root)
    run_id = run_root.name
    public_helper_path = ensure_public_helper_lemma_lib(run_root)
    public_helper_snapshot = public_helper_pool_snapshot(public_helper_path)
    state: dict[str, Any] = {
        "generation": 0,
        "run_id": run_id,
        "case": args.case,
        "phase": "intake",
        "main_root": str(main_root),
        "run_root": str(run_root),
        "report_root": str(report_root),
        "target_files": target_files,
        "public_helper_lemma_lib": {
            key: public_helper_snapshot[key]
            for key in ("path", "sha256", "declaration_count", "helper_count")
        },
        "problem_context": _problem_context_from_args(args),
        "spec_freeze": _spec_freeze_baseline(
            main_root=main_root,
            target_files=target_files,
            functions=_freeze_spec_functions(args),
        ),
        "max_compact_attempts": args.max_compact_attempts,
        "max_witnesses_per_group": args.max_witnesses_per_group,
        "max_parallel_group_workers": args.max_parallel_group_workers,
        "source_version": None,
        "source_goal_version": None,
        "dune_preparation": None,
        "rounds": {},
        "attempts": {},
        "annotation_session": None,
        "accepted_rounds": {},
        "next_actions": [],
        "waiting_for": [],
        "current_blockers": [],
        "final_candidate": None,
        "final_apply": None,
        "final_check": None,
        "created_at": _utc(),
    }
    state["source_version"] = _source_version_for_state(state, annotated=False)
    _write_target_topology_anchor(
        main_root=main_root,
        report_root=report_root,
        state=state,
    )
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
