#!/usr/bin/env python3
"""Run creation, durable controller state, versions, logs, and snapshots.

This module is internal to controller.py.  It owns the controller's durable
state primitives; callers outside the controller use the controller CLI.
"""

# ruff: noqa: E402 -- controller modules resolve the internal vc-proving directory at runtime.

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parents[1] / "vc-proving" / "scripts"
if str(VC_PROVING_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from path_utils import (
    controller_state_path,
    ensure_run_root,
    is_run_root_name,
    main_root_from_run_root,
    reports_root,
    run_logs_path,
    target_files_for_c,
    write_json,
)
from proof_manual_utils import (
    ensure_unique_lemma_names,
    lemma_statement_hash,
    parse_manual_file,
)


SCHEMA_STATE = "qcp-controller-run-state/v5"
SCHEMA_RUN_LOG = "qcp-controller-run-log/v3"
SCHEMA_TIMING_SUMMARY = "qcp-timing-summary/v4"
GENERATED_KEYS = (
    "goal_file",
    "proof_auto_file",
    "proof_manual_file",
    "goal_check_file",
    "proof_diagnostics_file",
    "diagnostics_snapshot",
)


def _utc() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z")


def _parse_utc(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def _elapsed_between(started_at: str, finished_at: str) -> float:
    return round(max(0.0, (_parse_utc(finished_at) - _parse_utc(started_at)).total_seconds()), 6)


def _json_load(path: Path, default: Any | None = None) -> Any:
    if not path.is_file():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.expanduser().resolve().relative_to(root.expanduser().resolve())
        return True
    except ValueError:
        return False


def _relative_path(path: Path, root: Path) -> str:
    return path.expanduser().resolve().relative_to(root.expanduser().resolve()).as_posix()


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
        "problem_statement": "\n\n".join(part.strip() for part in statement_parts if part.strip()),
        "target_function": str(args.target_function or ""),
        "expected_behavior": str(args.expected_behavior or ""),
        "input_output_contract": str(args.input_output_contract or ""),
        "spec_hint": [str(item) for item in args.spec_hint],
        "preferred_hidden_properties": [str(item) for item in args.preferred_hidden_property],
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
    files: list[dict[str, Any]] = []
    digest_input: list[dict[str, Any]] = []
    for path in paths:
        resolved = path.expanduser().resolve()
        relative = _relative_path(resolved, main_root)
        state = "present" if resolved.is_file() else "missing"
        entry: dict[str, Any] = {
            "relative_path": relative,
            "sha256": _file_digest(resolved) if state == "present" else None,
            "state": state,
        }
        role = (roles or {}).get(relative)
        if role:
            entry["role"] = role
        files.append(entry)
        digest_entry = {key: entry[key] for key in ("relative_path", "sha256", "state")}
        if role:
            digest_entry["role"] = role
        digest_input.append(digest_entry)
    digest_input.sort(key=lambda item: (str(item["relative_path"]), str(item.get("role", ""))))
    digest = hashlib.sha256(json.dumps(digest_input, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {
        "schema_version": "qcp-source-version/v3",
        "digest": digest,
        "files": files,
    }


def _source_version_for_state(state: dict[str, Any], *, annotated: bool) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    target = state["target_files"]
    roles = {
        target["c_file"]: "target-c-annotated" if annotated else "target-c",
        target["formal_case_lib"]: "formal-case-lib-seed",
    }
    return _source_version(
        [main_root / target["c_file"], main_root / target["formal_case_lib"]],
        main_root=main_root,
        roles=roles,
    )


def _source_goal_version(state: dict[str, Any]) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    target = state["target_files"]
    generated: list[dict[str, Any]] = []
    for key in GENERATED_KEYS:
        path = main_root / target[key]
        generated.append(
            {
                "relative_path": target[key],
                "role": key,
                "state": "present" if path.is_file() else "missing",
                "sha256": _file_digest(path) if path.is_file() else None,
            }
        )
    manual = main_root / target["proof_manual_file"]
    _prelude, lemmas = parse_manual_file(manual.read_text(encoding="utf-8"))
    ensure_unique_lemma_names(lemmas)
    witnesses = [{"name": str(lemma["name"]), "statement_hash": lemma_statement_hash(lemma)} for lemma in lemmas]
    payload = {
        "generated_files": generated,
        "target_witnesses": [item["name"] for item in witnesses],
        "witness_statement_hashes": {item["name"]: item["statement_hash"] for item in witnesses},
    }
    return {
        "schema_version": "qcp-source-goal-version/v3",
        "digest": hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
        **payload,
    }


def _current_version_errors(state: dict[str, Any]) -> list[str]:
    """Compare current root inputs/goals with the accepted annotation versions."""

    errors: list[str] = []
    try:
        current_source = _source_version_for_state(state, annotated=True)
        current_goal = _source_goal_version(state)
    except (OSError, ValueError) as exc:
        return [f"current formal state cannot be versioned: {exc}"]
    saved_source = str((state.get("source_version") or {}).get("digest") or "")
    saved_goal = str((state.get("source_goal_version") or {}).get("digest") or "")
    if not saved_source or current_source["digest"] != saved_source:
        errors.append("current target C or formal_case_lib differs from source_version")
    if not saved_goal or current_goal["digest"] != saved_goal:
        errors.append("current generated/manual files differ from source_goal_version")
    accepted = state.get("accepted_rounds", {}).get("annotation", {})
    if accepted.get("source_version") != saved_source or accepted.get("source_goal_version") != saved_goal:
        errors.append("accepted annotation versions do not match controller state")
    return errors


def _ensure_formal_case_lib_seed(state: dict[str, Any]) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    relative = str(state["target_files"]["formal_case_lib"])
    path = main_root / relative
    if path.is_file():
        return {
            "status": "existing",
            "relative_path": relative,
            "sha256": _file_digest(path),
        }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "Require Import Coq.Lists.List.\n"
        "Require Import Coq.ZArith.ZArith.\n"
        "Require Import Coq.micromega.Lia.\n"
        "Require Import AUXLib.ListLib.\n\n"
        "Import ListNotations.\n"
        "Local Open Scope Z_scope.\n",
        encoding="utf-8",
    )
    return {
        "status": "created",
        "relative_path": relative,
        "sha256": _file_digest(path),
    }


def _run_root_from_id(main_root: Path, run_id: str) -> Path:
    if Path(run_id).name != run_id or not is_run_root_name(run_id):
        raise SystemExit(f"invalid run id: {run_id}")
    owner = main_root.expanduser().resolve()
    path = (owner / "verification_runs" / run_id).resolve()
    if path.parent != owner / "verification_runs":
        raise SystemExit(f"run is outside the main root: {path}")
    if not path.is_dir():
        raise SystemExit(f"run not found: {path}")
    return path


def _load_state(run_root: Path) -> dict[str, Any]:
    path = controller_state_path(run_root)
    state = _json_load(path)
    if not isinstance(state, dict):
        raise SystemExit(f"controller state is missing or invalid: {path}")
    if state.get("schema_version") != SCHEMA_STATE:
        raise SystemExit(f"unsupported controller state schema: {state.get('schema_version')}")
    if Path(str(state.get("run_root", ""))).resolve() != run_root.expanduser().resolve():
        raise SystemExit("controller state run_root does not match its fixed run directory")
    if Path(str(state.get("main_root", ""))).resolve() != main_root_from_run_root(run_root):
        raise SystemExit("controller state main_root does not own its fixed run directory")
    return state


def _append_log(run_root: Path, record: dict[str, Any]) -> None:
    path = run_logs_path(run_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True, ensure_ascii=True) + "\n")


def _append_event(run_root: Path, state: dict[str, Any], event: str, **details: Any) -> None:
    _append_log(
        run_root,
        {
            "schema_version": SCHEMA_RUN_LOG,
            "at": _utc(),
            "event": event,
            "phase": state.get("phase"),
            "details": details,
        },
    )


def _save_state(run_root: Path, state: dict[str, Any]) -> None:
    state["updated_at"] = _utc()
    write_json(controller_state_path(run_root), state)
    _write_timing_summary(state)


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
            float(elapsed_seconds) if elapsed_seconds is not None else _elapsed_between(started_at, finished_at),
            6,
        )
    attempt.setdefault("timing", {}).setdefault(stage, []).append(interval)
    return interval


def _record_elapsed_stage(attempt: dict[str, Any], stage: str, elapsed_seconds: float) -> None:
    finished = datetime.now(timezone.utc)
    started = finished.timestamp() - max(0.0, float(elapsed_seconds))
    _record_timing_interval(
        attempt,
        stage,
        started_at=datetime.fromtimestamp(started, timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z"),
        finished_at=finished.isoformat(timespec="microseconds").replace("+00:00", "Z"),
        elapsed_seconds=elapsed_seconds,
    )


def _aggregate_stage(name: str, intervals: list[dict[str, Any]]) -> dict[str, Any] | None:
    if not intervals:
        return None
    starts = [str(item["started_at"]) for item in intervals if item.get("started_at")]
    if not starts:
        return None
    finished = [str(item["finished_at"]) for item in intervals if item.get("finished_at")]
    stage: dict[str, Any] = {
        "name": name,
        "started_at": min(starts, key=_parse_utc),
    }
    if len(intervals) > 1:
        stage["calls"] = len(intervals)
    if len(finished) == len(intervals):
        stage["finished_at"] = max(finished, key=_parse_utc)
        stage["elapsed_seconds"] = round(sum(float(item.get("elapsed_seconds", 0.0)) for item in intervals), 6)
    return stage


def _lifecycle_stage(name: str, started_at: str | None, finished_at: str | None) -> dict[str, Any] | None:
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
        entry = {"round": attempt["round"], "phase": "vc-proving" if phase == "vc-proving-preparing" else phase}
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
            starts = [str(item["started_at"]) for item in group_intervals if item.get("started_at")]
            ends = [str(item["finished_at"]) for item in group_intervals if item.get("finished_at")]
        else:
            groups = list((attempt.get("groups") or {}).values())
            starts = [str(group["started_at"]) for group in groups if group.get("started_at")]
            ends = [str(group["returned_at"]) for group in groups if group.get("returned_at")]
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
            "annotation-checking",
            "controller-review",
            "controller-acceptance-check",
        ),
        "vc-checking": ("controller-review", "controller-plan-check"),
        "vc-proving-preparing": ("preparing", "group-coq-check", "group-review", "parent-verify"),
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
    write_json(
        _timing_path(Path(str(state["report_root"]))),
        {
            "schema_version": SCHEMA_TIMING_SUMMARY,
            "annotation_attempts": annotation,
            "rounds": rounds,
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
    state = _load_state(run_root)
    attempt: dict[str, Any] | None = None
    stage: str | None = None
    if command in {"annotation-check-round", "vc-checking-check-round", "vc-proving-preparing", "vc-proving-verify"}:
        round_state = state.get("rounds", {}).get(str(round_id), {})
        attempt = state.get("attempts", {}).get(str(round_state.get("current_attempt")))
        stage = {
            "annotation-check-round": "controller-acceptance-check",
            "vc-checking-check-round": "controller-plan-check",
            "vc-proving-preparing": "preparing",
            "vc-proving-verify": "parent-verify",
        }[command]
    elif command == "review-attempt" and attempt_id:
        if ":" in attempt_id:
            proving_round, _group = attempt_id.split(":", 1)
            attempt = state.get("attempts", {}).get(proving_round)
            stage = "group-review"
        else:
            attempt = state.get("attempts", {}).get(attempt_id)
            stage = "controller-review"
    if isinstance(attempt, dict) and stage:
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
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    round_state = state.get("rounds", {}).get(args.round, {})
    attempt = state.get("attempts", {}).get(str(round_state.get("current_attempt")))
    if not isinstance(attempt, dict) or attempt.get("phase") != "annotation":
        raise SystemExit(f"annotation round not found for timing stage: {args.round}")
    if attempt.get("status") != "running" or not attempt.get("started_at"):
        raise SystemExit("annotation attempt must be running before timing annotation-checking")
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
        intervals[-1]["elapsed_seconds"] = _elapsed_between(str(intervals[-1]["started_at"]), finished_at)
    _save_state(run_root, state)
    return 0


def _snapshot_files(state: dict[str, Any], destination: Path) -> None:
    main_root = Path(str(state["main_root"]))
    destination.mkdir(parents=True, exist_ok=True)
    for key in ("c_file", "formal_case_lib", *GENERATED_KEYS):
        relative = str(state["target_files"][key])
        source = main_root / relative
        if source.is_file():
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)


def _snapshot_digests(root: Path, relatives: list[str]) -> dict[str, str | None]:
    return {relative: _file_digest(root / relative) if (root / relative).is_file() else None for relative in relatives}


def _archive_annotation_stage(state: dict[str, Any], attempt: dict[str, Any], stage: str) -> None:
    destination = Path(str(attempt["annotation_history_directory"])) / stage
    if destination.exists():
        shutil.rmtree(destination)
    _snapshot_files(state, destination)


def _annotation_changed_files(state: dict[str, Any], attempt: dict[str, Any]) -> list[str]:
    history = Path(str(attempt["annotation_history_directory"]))
    relatives = [str(state["target_files"][key]) for key in ("c_file", "formal_case_lib", *GENERATED_KEYS)]
    before = _snapshot_digests(history / "before", relatives)
    after = _snapshot_digests(history / "after", relatives)
    return [relative for relative in relatives if before[relative] != after[relative]]


def init_run(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    if args.timestamp is not None and re.fullmatch(r"\d{14}", str(args.timestamp)) is None:
        raise SystemExit("--timestamp must contain exactly 14 digits (YYYYMMDDhhmmss)")
    if args.max_compact_attempts < 1:
        raise SystemExit("--max-compact-attempts must be positive")
    if args.max_witnesses_per_group < 1:
        raise SystemExit("--max-witnesses-per-group must be positive")
    target = Path(args.target_c_file).expanduser()
    if not target.is_absolute():
        target = main_root / target
    target = target.resolve()
    if not target.is_file() or not _is_relative_to(target, main_root):
        raise SystemExit(f"target C file must exist under main root: {target}")
    target_rel = _relative_path(target, main_root)
    run_root = ensure_run_root(main_root, args.case, timestamp=args.timestamp)
    report_root = reports_root(run_root)
    run_id = run_root.name
    target_files = target_files_for_c(target_rel)
    state: dict[str, Any] = {
        "schema_version": SCHEMA_STATE,
        "run_id": run_id,
        "case": args.case,
        "phase": "intake",
        "main_root": str(main_root),
        "run_root": str(run_root),
        "report_root": str(report_root),
        "target_files": target_files,
        "problem_context": _problem_context_from_args(args),
        "max_compact_attempts": args.max_compact_attempts,
        "max_witnesses_per_group": args.max_witnesses_per_group,
        "source_version": None,
        "source_goal_version": None,
        "rounds": {},
        "attempts": {},
        "annotation_session": None,
        "accepted_rounds": {},
        "accepted_groups": {},
        "next_actions": [],
        "current_blockers": [],
        "final_candidate": None,
        "final_apply": None,
        "final_check": None,
        "created_at": _utc(),
    }
    seed = _ensure_formal_case_lib_seed(state)
    state["source_version"] = _source_version_for_state(state, annotated=False)
    _append_event(run_root, state, "run-initialized", run_id=run_id, formal_case_lib_seed=seed["status"])
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
