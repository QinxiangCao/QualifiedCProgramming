#!/usr/bin/env python3
"""Attempt lifecycle, structured-result review, retry, and stale propagation.

This module is internal to controller.py. It reviews phase-agent and group
attempts but never performs main-owned acceptance checks or launches agents.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from coq_tooling import infer_case_config, run_coqc_check
from path_utils import coq_identifier_slug, render_group_worker_input, run_builds_root
from verify_group_results import validate_group_for_acceptance

from controller_state import (
    _annotation_changed_files,
    _append_event,
    _archive_annotation_stage,
    _current_version_errors,
    _file_digest,
    _json_load,
    _load_state,
    _elapsed_between,
    _record_timing_interval,
    _run_root_from_id,
    _save_state,
    _utc,
)
from controller_rounds import VC_PROVING_PHASE, _init_round_attempt, _sync_group_actions


ALLOWED_RESULT_STATUSES = {"completed", "blocked", "stale", "compact-error", "returned"}


def _attempt_artifact(attempt: dict[str, Any], key: str) -> Path:
    return Path(str(attempt[key]))


def _artifact_digests(paths: dict[str, Path]) -> dict[str, str]:
    missing = [str(path) for path in paths.values() if not path.is_file()]
    if missing:
        raise SystemExit("returned attempt artifacts are missing: " + ", ".join(missing))
    return {key: _file_digest(path) for key, path in paths.items()}


def _artifact_integrity_errors(paths: dict[str, Path], expected: dict[str, str] | None) -> list[str]:
    if not isinstance(expected, dict):
        return ["returned attempt artifacts were not sealed"]
    errors: list[str] = []
    for key, path in paths.items():
        if not path.is_file():
            errors.append(f"sealed {key} artifact is missing: {path}")
        elif _file_digest(path) != expected.get(key):
            errors.append(f"sealed {key} artifact changed after return: {path}")
    return errors


def _queue_annotation_feedback(state: dict[str, Any], source_attempt: str, reason: str) -> None:
    """Expose the main-owned transition that appends this blocker to the one annotation agent."""

    state["next_actions"] = [
        {
            "id": f"annotation-feedback-{source_attempt.replace(':', '-')}",
            "kind": "main-owned-action",
            "action": "retry-round",
            "phase": "annotation",
            "reason": reason,
            "previous_attempt": source_attempt,
        }
    ]


def _proving_manifest_errors(proving: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    for path_field, digest_field, label in (
        ("base_manifest", "base_manifest_sha256", "base_manifest"),
        ("group_workers_manifest", "group_workers_manifest_sha256", "group_workers_manifest"),
    ):
        path = Path(str(proving.get(path_field) or ""))
        expected = str(proving.get(digest_field) or "")
        if not path.is_file() or not expected:
            errors.append(f"{label} integrity record is missing")
        elif _file_digest(path) != expected:
            errors.append(f"{label} changed after vc-proving preparation")
    return errors


def _find_round_attempt(state: dict[str, Any], identifier: str) -> dict[str, Any] | None:
    if identifier in state["attempts"] and state["attempts"][identifier].get("phase") != VC_PROVING_PHASE:
        return state["attempts"][identifier]
    path = Path(identifier).expanduser().resolve()
    for attempt in reversed(list(state["attempts"].values())):
        if attempt.get("phase") == VC_PROVING_PHASE:
            continue
        candidates = {
            Path(str(attempt["report_directory"])).resolve(),
            Path(str(attempt["report"])).resolve(),
        }
        if path in candidates:
            return attempt
    return None


def _find_group_attempt(state: dict[str, Any], identifier: str) -> tuple[dict[str, Any], str] | None:
    if ":" in identifier:
        round_id, group_id = identifier.split(":", 1)
        attempt = state["attempts"].get(round_id)
        if attempt and attempt.get("phase") == VC_PROVING_PHASE and group_id in attempt.get("groups", {}):
            return attempt, group_id
    path = Path(identifier).expanduser().resolve()
    for attempt in state["attempts"].values():
        if attempt.get("phase") != VC_PROVING_PHASE:
            continue
        manifest = _json_load(Path(str(attempt["group_workers_manifest"])), {})
        for group in manifest.get("groups", []) if isinstance(manifest, dict) else []:
            report = Path(str(group.get("report_directory", ""))).resolve() / "group_worker_report.json"
            if path in {report, report.parent}:
                return attempt, str(group["id"])
    return None


def mark_attempt_started(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _find_round_attempt(state, args.attempt)
    if attempt is not None:
        if attempt.get("status") in {"stale", "superseded", "accepted"}:
            raise SystemExit(f"attempt is not startable from status {attempt.get('status')}")
        if attempt.get("phase") == "annotation":
            if attempt.get("status") != "prepared":
                raise SystemExit(f"annotation attempt is not prepared for delivery: {attempt.get('status')}")
            input_path = Path(str(attempt["input"]))
            if not input_path.is_file() or _file_digest(input_path) != attempt.get("input_sha256"):
                raise SystemExit("annotation agent_input.md changed after controller validation")
        attempt["status"] = "running"
        attempt["started_at"] = _utc()
        if attempt.get("phase") == "annotation" and isinstance(state.get("annotation_session"), dict):
            state["annotation_session"]["status"] = "running"
    else:
        found = _find_group_attempt(state, args.attempt)
        if found is None:
            raise SystemExit(f"attempt not found: {args.attempt}")
        proving, group_id = found
        if proving.get("status") != "groups-ready":
            raise SystemExit("group attempt does not belong to the current groups-ready vc-proving round")
        proving["groups"][group_id]["status"] = "running"
        started_at = _utc()
        proving["groups"][group_id]["started_at"] = started_at
        intervals = proving.setdefault("timing", {}).setdefault("group-work", [])
        _record_timing_interval(proving, "group-work", started_at=started_at)
        proving["groups"][group_id]["timing_interval_index"] = len(intervals) - 1
    state["next_actions"] = [item for item in state["next_actions"] if item.get("attempt_id") != args.attempt]
    _append_event(run_root, state, "attempt-started", attempt=args.attempt)
    _save_state(run_root, state)
    return 0


def mark_attempt_returned(args: argparse.Namespace) -> int:
    if args.result_status not in ALLOWED_RESULT_STATUSES:
        raise SystemExit(f"invalid result status: {args.result_status}")
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _find_round_attempt(state, args.attempt)
    if attempt is not None:
        if attempt.get("status") in {"stale", "superseded", "accepted"}:
            raise SystemExit(f"attempt is not returnable from status {attempt.get('status')}")
        if attempt.get("status") != "running" or not attempt.get("started_at"):
            raise SystemExit("attempt must be marked started before it can be returned")
        attempt["status"] = args.result_status
        attempt["returned_at"] = _utc()
        attempt["artifact_sha256"] = _artifact_digests(
            {
                "report": Path(str(attempt["report"])),
                "output": Path(str(attempt["output"])),
            }
        )
        if attempt["phase"] == "annotation":
            _archive_annotation_stage(state, attempt, "after")
            attempt["changed_files"] = _annotation_changed_files(state, attempt)
            if isinstance(state.get("annotation_session"), dict):
                state["annotation_session"]["status"] = "returned"
    else:
        found = _find_group_attempt(state, args.attempt)
        if found is None:
            raise SystemExit(f"attempt not found: {args.attempt}")
        proving, group_id = found
        if proving.get("status") != "groups-ready":
            raise SystemExit("group attempt does not belong to the current groups-ready vc-proving round")
        if proving["groups"][group_id].get("status") != "running" or not proving["groups"][group_id].get("started_at"):
            raise SystemExit("group attempt must be marked started before it can be returned")
        proving["groups"][group_id]["status"] = args.result_status
        returned_at = _utc()
        proving["groups"][group_id]["returned_at"] = returned_at
        interval_index = int(proving["groups"][group_id].get("timing_interval_index", -1))
        intervals = proving.setdefault("timing", {}).setdefault("group-work", [])
        if interval_index < 0 or interval_index >= len(intervals) or intervals[interval_index].get("finished_at"):
            raise SystemExit("group attempt timing interval is missing or already closed")
        intervals[interval_index]["finished_at"] = returned_at
        intervals[interval_index]["elapsed_seconds"] = _elapsed_between(
            str(intervals[interval_index]["started_at"]),
            returned_at,
        )
        manifest = _json_load(Path(str(proving["group_workers_manifest"])), {})
        group = next(
            (item for item in manifest.get("groups", []) if str(item.get("id")) == group_id),
            None,
        )
        if not isinstance(group, dict):
            raise SystemExit(f"returned group is missing from the current manifest: {group_id}")
        report_directory = Path(str(group["report_directory"]))
        proving["groups"][group_id]["artifact_sha256"] = _artifact_digests(
            {
                "report": report_directory / "group_worker_report.json",
                "output": report_directory / "group_worker_output.md",
            }
        )
    _append_event(
        run_root,
        state,
        "attempt-returned",
        attempt=args.attempt,
        result_status=args.result_status,
    )
    _save_state(run_root, state)
    return 0


def _phase_result(report: dict[str, Any], phase: str) -> dict[str, Any]:
    del phase
    return report if isinstance(report, dict) else {}


def _group_tooling(
    state: dict[str, Any], proving: dict[str, Any], group: dict[str, Any]
) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    run_root = Path(str(state["run_root"]))
    target = state["target_files"]
    directory = Path(str(group["directory"]))
    case = infer_case_config(main_root, (main_root / target["proof_manual_file"]).parent)
    build = run_builds_root(run_root) / proving["round"] / directory.name / "src"
    coq_group_name = coq_identifier_slug(directory.name)
    goal_module = Path(str(target["goal_file"])).stem
    proof_auto_module = Path(str(target["proof_auto_file"])).stem
    proof_manual_module = Path(str(target["proof_manual_file"])).stem
    return {
        "target_file": Path(".coq_group_checks") / f"{proof_manual_module}_{coq_group_name}_check.v",
        "build_workspace": build,
        "group_check": {
            "case_theory": case["active_theory"],
            "require_modules": [
                goal_module,
                proof_auto_module,
                proof_manual_module,
            ],
            "assigned_witnesses": [str(name) for name in group["witnesses"]],
        },
        "overlays": {
            Path(target["proof_manual_file"]): Path(str(group["proof_manual"])),
            Path(target["formal_case_lib"]): Path(str(group["group_worker_lib"])),
        },
        "debug_script": Path(".coq_debug") / f"{coq_group_name}.v",
    }


def _review_group(state: dict[str, Any], proving: dict[str, Any], group_id: str) -> tuple[str, list[str], dict[str, Any] | None]:
    integrity_errors = _proving_manifest_errors(proving)
    if integrity_errors:
        return "invalid", integrity_errors, None
    manifest = _json_load(Path(str(proving["group_workers_manifest"])), {})
    group = next(
        (item for item in manifest.get("groups", []) if str(item.get("id")) == group_id),
        None,
    )
    if not isinstance(group, dict):
        return "invalid", ["group missing from current manifest"], None
    report_directory = Path(str(group["report_directory"]))
    group_artifact_errors = _artifact_integrity_errors(
        {
            "report": report_directory / "group_worker_report.json",
            "output": report_directory / "group_worker_output.md",
        },
        proving.get("groups", {}).get(group_id, {}).get("artifact_sha256"),
    )
    if group_artifact_errors:
        return "invalid", group_artifact_errors, None
    report = _json_load(report_directory / "group_worker_report.json", {})
    if report.get("schema_version") != "qcp-group-worker-report/v2":
        return "invalid", ["invalid group report schema_version"], None
    extra = set(report) - {"schema_version", "status", "source_goal_version", "blockers"}
    if extra:
        return "invalid", [f"group report contains unsupported fields: {sorted(extra)}"], None
    status = str(report.get("status") or "pending")
    errors: list[str] = []
    errors.extend(_current_version_errors(state))
    current_goal = state.get("source_goal_version", {}).get("digest")
    if report.get("source_goal_version") != current_goal:
        errors.append("group source_goal_version is stale")
    evidence: dict[str, Any] | None = None
    if status == "completed":
        if report.get("blockers"):
            errors.append("completed group cannot contain blockers or errors")
        if not errors:
            try:
                errors.extend(
                    validate_group_for_acceptance(
                        Path(str(proving["group_workers_manifest"])),
                        group_id=group_id,
                        main_root=Path(str(state["main_root"])),
                        expected_proof_manual=str(state["target_files"]["proof_manual_file"]),
                        expected_formal_case_lib=str(state["target_files"]["formal_case_lib"]),
                    )
                )
            except (OSError, ValueError, json.JSONDecodeError, SystemExit) as exc:
                errors.append(f"group candidate validation failed: {exc}")
        if not errors:
            tooling = _group_tooling(state, proving, group)
            evidence = run_coqc_check(
                workspace_root=Path(str(state["main_root"])),
                build_workspace=tooling["build_workspace"],
                target_file=tooling["target_file"],
                target_kind="group-check",
                source_goal_version=str(current_goal),
                group_check=tooling["group_check"],
                overlays=tooling["overlays"],
            )
            if evidence.get("status") != "passed":
                errors.append("controller group check failed")
    return status, errors, evidence


def review_attempt(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _find_round_attempt(state, args.attempt)
    if attempt is None:
        found = _find_group_attempt(state, args.attempt)
        if found is None:
            raise SystemExit(f"attempt not found: {args.attempt}")
        proving, group_id = found
        if proving.get("status") != "groups-ready":
            raise SystemExit("group attempt does not belong to the current groups-ready vc-proving round")
        status, errors, evidence = _review_group(state, proving, group_id)
        if errors:
            proving["groups"][group_id]["status"] = "invalid-report"
            proving["groups"][group_id]["review_errors"] = errors
            if evidence:
                proving["groups"][group_id]["group_check"] = {
                    key: evidence.get(key)
                    for key in ("status", "returncode", "source_goal_version", "first_diagnostic")
                }
            result_status = "invalid-report"
        elif status == "completed":
            proving["groups"][group_id]["status"] = "accepted"
            proving["groups"][group_id]["group_check"] = {
                key: evidence.get(key)
                for key in ("status", "returncode", "source_goal_version")
            }
            state.setdefault("accepted_groups", {}).setdefault(proving["round"], [])
            if group_id not in state["accepted_groups"][proving["round"]]:
                state["accepted_groups"][proving["round"]].append(group_id)
            result_status = "accepted"
        elif status == "compact-error":
            group_state = proving["groups"][group_id]
            attempt_index = int(group_state.get("attempt_index", 1))
            manifest = _json_load(Path(str(proving["group_workers_manifest"])), {})
            group_entry = next(item for item in manifest["groups"] if str(item["id"]) == group_id)
            group_state.setdefault("compact_attempts", []).append(
                {
                    "attempt_index": attempt_index,
                    "recorded_at": _utc(),
                }
            )
            if attempt_index < int(state["max_compact_attempts"]):
                group_state["attempt_index"] = attempt_index + 1
                group_state["status"] = "prepared"
                report_dir = Path(str(group_entry["report_directory"]))
                input_path = report_dir / "group_worker_input.md"
                input_path.write_text(
                    render_group_worker_input(
                        group_entry,
                        source_goal_version=str(state["source_goal_version"]["digest"]),
                        formal_case_lib=str(state["target_files"]["formal_case_lib"]),
                        report_dir=report_dir,
                        attempt_index=attempt_index + 1,
                        previous_compact_attempts=len(group_state["compact_attempts"]),
                    ).rstrip()
                    + "\n",
                    encoding="utf-8",
                )
                result_status = "compact-retry-prepared"
            else:
                group_state["status"] = "blocked"
                group_state["blocker"] = "compact-error-retry-exhausted"
                result_status = "compact-error-retry-exhausted"
        else:
            proving["groups"][group_id]["status"] = status
            result_status = status
        _sync_group_actions(state, proving)
        if result_status == "blocked":
            _queue_annotation_feedback(state, f"{proving['round']}:{group_id}", "group-worker-blocked")
        _append_event(
            run_root,
            state,
            "group-attempt-reviewed",
            group_id=group_id,
            status=result_status,
            errors=errors,
        )
        _save_state(run_root, state)
        print(json.dumps({"status": result_status, "errors": errors}, indent=2))
        return (
            0
            if result_status
            in {
                "accepted",
                "blocked",
                "stale",
                "compact-retry-prepared",
                "compact-error-retry-exhausted",
            }
            else 1
        )

    if attempt.get("status") in {"stale", "superseded", "accepted"}:
        raise SystemExit(f"attempt is not reviewable from status {attempt.get('status')}")
    report_path = _attempt_artifact(attempt, "report")
    report = _json_load(report_path, {})
    result = _phase_result(report, str(attempt["phase"]))
    status = str(result.get("status") or "pending")
    errors: list[str] = []
    errors.extend(
        _artifact_integrity_errors(
            {
                "report": report_path,
                "output": _attempt_artifact(attempt, "output"),
            },
            attempt.get("artifact_sha256"),
        )
    )
    if report.get("schema_version") != "qcp-agent-report/v3":
        errors.append("invalid agent report schema_version")
    allowed_report_fields = (
        {"schema_version", "status", "changed_files", "checks", "blockers"}
        if attempt["phase"] == "annotation"
        else {"schema_version", "status", "source_goal_version", "blockers"}
    )
    extra_report_fields = set(report) - allowed_report_fields
    if extra_report_fields:
        errors.append(f"agent report contains unsupported fields: {sorted(extra_report_fields)}")
    if status == "completed" and result.get("blockers"):
        errors.append("completed result cannot contain blockers")
    if attempt["phase"] == "annotation":
        input_path = Path(str(attempt["input"]))
        if not input_path.is_file() or _file_digest(input_path) != attempt.get("input_sha256"):
            errors.append("annotation agent_input.md changed after controller validation")
        if not (Path(str(attempt["annotation_history_directory"])) / "after").is_dir():
            _archive_annotation_stage(state, attempt, "after")
        attempt["changed_files"] = _annotation_changed_files(state, attempt)
        declared_changed = result.get("changed_files") if isinstance(result.get("changed_files"), list) else []
        if set(str(item) for item in declared_changed) != set(attempt["changed_files"]):
            errors.append("annotation report changed_files does not match the archived diff")
        allowed = set(attempt.get("allowed_write_paths", []))
        if not set(attempt["changed_files"]) <= allowed:
            errors.append("annotation changed paths outside allowed_write_paths")
        if status == "completed":
            checks = result.get("checks") if isinstance(result.get("checks"), dict) else {}
            for field in ("symexec", "formal_case_lib", "annotation_checking"):
                if checks.get(field) != "passed":
                    errors.append(f"completed annotation requires checks.{field} == passed")
    elif attempt["phase"] == "vc-checking" and status == "completed":
        expected_goal = str(state.get("source_goal_version", {}).get("digest") or "")
        if result.get("source_goal_version") != expected_goal:
            errors.append("vc-checking result source_goal_version is stale")
        if result.get("changed_files"):
            errors.append("vc-checking completed result must not declare formal file changes")
        errors.extend(_current_version_errors(state))
        if str((state.get("source_version") or {}).get("digest") or "") != attempt.get("source_version"):
            errors.append("vc-checking input source_version is stale")
    if errors:
        attempt["status"] = "invalid-report"
        attempt["review_errors"] = errors
        attempt["finished_at"] = _utc()
        result_status = "invalid-report"
    elif status == "completed":
        attempt["status"] = "ready-for-main-check"
        result_status = "ready-for-main-check"
        if attempt.get("phase") == "annotation" and isinstance(state.get("annotation_session"), dict):
            state["annotation_session"]["status"] = "awaiting-main-check"
        state["next_actions"] = [
            {
                "id": f"{attempt['phase']}-check-{attempt['round']}",
                "kind": "main-owned-action",
                "action": "annotation-check-round" if attempt["phase"] == "annotation" else "vc-checking-check-round",
                "round": attempt["round"],
                "attempt_id": attempt["attempt_id"],
            }
        ]
    else:
        attempt["status"] = status
        attempt["finished_at"] = _utc()
        result_status = status
        if attempt.get("phase") == "annotation" and isinstance(state.get("annotation_session"), dict):
            state["annotation_session"]["status"] = "idle"
        if status == "blocked":
            _queue_annotation_feedback(state, attempt["attempt_id"], f"{attempt['phase']}-blocked")
        elif status == "compact-error" and attempt.get("phase") == "annotation":
            _queue_annotation_feedback(state, attempt["attempt_id"], "annotation-compact-error")
    _append_event(
        run_root,
        state,
        "round-attempt-reviewed",
        attempt=attempt["attempt_id"],
        status=result_status,
        errors=errors,
    )
    _save_state(run_root, state)
    print(json.dumps({"status": result_status, "errors": errors}, indent=2))
    return 0 if result_status in {"ready-for-main-check", "blocked", "stale", "compact-error"} else 1


def _attempt_for_round(state: dict[str, Any], round_id: str, expected_phase: str) -> dict[str, Any]:
    round_state = state["rounds"].get(round_id)
    if not isinstance(round_state, dict) or round_state.get("phase") != expected_phase:
        raise SystemExit(f"{expected_phase} round not found: {round_id}")
    return state["attempts"][round_state["current_attempt"]]


def _invalidate_downstream(state: dict[str, Any], phase: str, reason: str) -> None:
    """Mark all conclusions downstream of a retry stale and clear live pointers."""

    stale_phases = {"vc-checking", VC_PROVING_PHASE}
    if phase == "annotation":
        stale_phases.add("annotation")
        state["source_goal_version"] = None
    for attempt in state.get("attempts", {}).values():
        if attempt.get("phase") in stale_phases and attempt.get("status") not in {
            "superseded",
            "stale",
        }:
            attempt["status"] = "stale"
            attempt["stale_reason"] = reason
            attempt.setdefault("finished_at", _utc())
    accepted_keys = {"vc-checking", VC_PROVING_PHASE}
    if phase == "annotation":
        accepted_keys.add("annotation")
    for key in accepted_keys:
        state.get("accepted_rounds", {}).pop(key, None)
    state["accepted_groups"] = {}
    state["final_candidate"] = None
    final_apply = state.get("final_apply") if isinstance(state.get("final_apply"), dict) else {}
    if final_apply.get("status") == "passed":
        raise SystemExit("cannot retry while a final candidate is applied; run final-check so it passes or rolls back first")
    state["final_apply"] = None
    state["final_check"] = None
    state["current_blockers"] = []


def _feedback_source(state: dict[str, Any], identifier: str) -> tuple[dict[str, str], dict[str, Any]]:
    attempt = _find_round_attempt(state, identifier)
    if attempt is not None:
        markdown = _attempt_artifact(attempt, "output")
        report = _attempt_artifact(attempt, "report")
        source = {
            "phase": str(attempt["phase"]),
            "attempt_id": str(attempt["attempt_id"]),
            "markdown": str(markdown),
            "json": str(report),
        }
        integrity_errors = _artifact_integrity_errors(
            {"report": report, "output": markdown},
            attempt.get("artifact_sha256"),
        )
        if integrity_errors:
            raise SystemExit("annotation feedback artifacts are not immutable: " + "; ".join(integrity_errors))
        payload = _json_load(report, {})
    else:
        found = _find_group_attempt(state, identifier)
        if found is None:
            raise SystemExit(f"feedback attempt not found: {identifier}")
        proving, group_id = found
        manifest = _json_load(Path(str(proving["group_workers_manifest"])), {})
        group = next(
            (item for item in manifest.get("groups", []) if str(item.get("id")) == group_id),
            None,
        )
        if not isinstance(group, dict):
            raise SystemExit(f"feedback group is missing from the current manifest: {identifier}")
        report_directory = Path(str(group["report_directory"]))
        markdown = report_directory / "group_worker_output.md"
        report = report_directory / "group_worker_report.json"
        source = {
            "phase": "group-worker",
            "attempt_id": identifier,
            "markdown": str(markdown),
            "json": str(report),
        }
        integrity_errors = _artifact_integrity_errors(
            {"report": report, "output": markdown},
            proving.get("groups", {}).get(group_id, {}).get("artifact_sha256"),
        )
        if integrity_errors:
            raise SystemExit("annotation feedback artifacts are not immutable: " + "; ".join(integrity_errors))
        payload = _json_load(report, {})
    missing = [source[key] for key in ("markdown", "json") if not Path(source[key]).is_file()]
    if missing:
        raise SystemExit("annotation feedback requires both Markdown and JSON sources: " + ", ".join(missing))
    return source, payload if isinstance(payload, dict) else {}


def _current_annotation_attempt(state: dict[str, Any]) -> dict[str, Any]:
    session = state.get("annotation_session")
    if not isinstance(session, dict) or not session.get("current_attempt"):
        raise SystemExit("the run has no persistent annotation agent session")
    attempt = state.get("attempts", {}).get(str(session["current_attempt"]))
    if not isinstance(attempt, dict) or attempt.get("phase") != "annotation":
        raise SystemExit("persistent annotation session does not reference an annotation attempt")
    return attempt


def retry_round(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    feedback_sources: list[dict[str, str]] = []
    feedback_payload: dict[str, Any]
    if args.phase == "annotation":
        feedback, feedback_payload = _feedback_source(state, args.previous_attempt)
        feedback_sources.append(feedback)
        previous = _current_annotation_attempt(state)
        if feedback["attempt_id"] == previous["attempt_id"]:
            previous["status"] = "superseded"
            previous.setdefault("finished_at", _utc())
    else:
        previous = _find_round_attempt(state, args.previous_attempt)
        if previous is None or previous.get("phase") != args.phase:
            raise SystemExit("previous attempt does not match retry phase")
        previous["status"] = "superseded"
        previous.setdefault("finished_at", _utc())
        feedback_payload = _json_load(_attempt_artifact(previous, "report"), {})
    next_compact_index = int(previous.get("compact_attempt_index", 1))
    if "compact" in args.reason:
        next_compact_index += 1
        if next_compact_index > int(state["max_compact_attempts"]):
            previous["status"] = "blocked"
            previous.setdefault("finished_at", _utc())
            blocker = {
                "failure_class": "compact-error-retry-exhausted",
                "phase": args.phase,
                "previous_attempt": previous["attempt_id"],
            }
            state["current_blockers"] = [blocker]
            state["next_actions"] = []
            _append_event(run_root, state, "compact-retry-exhausted", **blocker)
            _save_state(run_root, state)
            print(json.dumps({"status": "blocked", "blocker": blocker}, indent=2))
            return 1
    previous_ref = {
        "round": previous["round"],
        "attempt_id": previous["attempt_id"],
        "report": str(_attempt_artifact(previous, "report")),
        "output": str(_attempt_artifact(previous, "output")),
        "reuse_policy": "read-only-reference",
    }
    result = _phase_result(feedback_payload, args.phase)
    lessons: list[dict[str, Any]] = []
    for item in result.get("blockers", []) if isinstance(result.get("blockers"), list) else []:
        lessons.append({"must_address": json.dumps(item, sort_keys=True)})
    if args.phase == "annotation" and isinstance(previous.get("main_check"), dict):
        lessons.append(
            {
                "must_address": "Controller main-check failure: "
                + json.dumps(previous["main_check"], sort_keys=True)
            }
        )
    _invalidate_downstream(state, args.phase, f"retry:{args.reason}")
    state["phase"] = args.phase
    attempt = _init_round_attempt(
        state,
        phase=args.phase,
        previous_attempts=[previous_ref],
        required_lessons=lessons,
        attempt_index=next_compact_index if "compact" in args.reason else 1,
        feedback_sources=feedback_sources,
        retry_reason=args.reason,
    )
    attempt["retry_reason"] = args.reason
    _append_event(
        run_root,
        state,
        "round-retried",
        phase=args.phase,
        previous=args.previous_attempt,
        reason=args.reason,
        annotation_session=(
            state["annotation_session"]["session_id"]
            if args.phase == "annotation" and isinstance(state.get("annotation_session"), dict)
            else None
        ),
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": attempt["status"],
                "attempt": attempt["attempt_id"],
                "action": state["next_actions"][0].get("action", state["next_actions"][0]["kind"]),
            },
            indent=2,
        )
    )
    return 0
