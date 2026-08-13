#!/usr/bin/env python3
"""Attempt lifecycle, controller validation, retry, and stale propagation.

This module is internal to controller.py. It validates phase-agent and group
attempts but never performs main-owned acceptance checks or launches agents.
"""

from __future__ import annotations

import argparse
import json
import os
import re
from pathlib import Path
from typing import Any

from controller_invocations import (
    finalize_invocation,
    handoff_payload,
    hydrate_actions,
)
from controller_rounds import (
    ANNOTATION_CAUSAL_FAILURE_CLASSES,
    ANNOTATION_GAP_FAILURE_CLASS,
    VC_PROVING_PHASE,
    VC_CHECKING_BLOCKER_RETRY_PHASES,
    _annotation_gap_feedback_records,
    _consider_broader_refactor,
    _delivery_message,
    _init_round_attempt,
    _reuse_group_artifacts_are_sealed,
    _running_deliveries,
    _sync_group_actions,
)
from controller_state import (
    _annotation_after_snapshot_errors,
    _annotation_changed_files,
    _annotation_current_changed_files,
    _append_event,
    _archive_annotation_stage,
    _current_version_errors,
    _elapsed_between,
    _file_digest,
    _generated_artifact_module_spellings_for_state,
    _json_load,
    _load_state,
    _record_timing_interval,
    _run_root_from_id,
    _state_transaction,
    _save_state,
    _snapshot_digests,
    _utc,
    _validated_annotation_attempt_paths,
    _validated_attempt_paths,
    _validated_proving_attempt_paths,
)
from coq_tooling import run_coqc_check
from file_integrity import sha256_bytes
from group_plan_utils import (
    group_check_names,
    group_entries_from_plan,
)
from path_utils import (
    coq_identifier_slug,
    fixed_path_under,
    group_build_workspace,
    group_debug_script_name,
    group_worker_commands,
    render_group_worker_input,
    write_text,
)
from prepare_group_workers import resolve_group_workers_manifest
from proof_manual_utils import HELPER_DECL_KINDS, parse_lib_declarations
from public_helper_utils import (
    apply_public_helper_declaration_plan,
    plan_public_helper_declarations,
    public_helper_lemma_lib_path,
    public_helper_pool_snapshot,
)
from verify_group_results import validate_group_for_acceptance_result

DELIVERY_ACTION_KINDS = {
    "spawn-attempt",
    "spawn-group-worker",
    "append-group-worker",
    "spawn-annotation-agent",
    "append-annotation-agent",
}

ANNOTATION_TERMINAL_STATUSES = {"completed", "blocked", "compact-error"}
PHASE_TERMINAL_STATUSES = {"completed", "blocked", "compact-error"}
GROUP_TERMINAL_STATUSES = {"completed", "blocked", "compact-error"}
MAX_IDENTICAL_INFRASTRUCTURE_BLOCKERS = 3


def _blocker_contract_errors(
    blocker: Any,
    *,
    context: str,
) -> list[str]:
    """Validate the one useful owner-authored failure fact."""

    if not isinstance(blocker, dict):
        return [f"{context} blocked result requires one blocker object"]
    required = {
        "failure_class",
        "kind",
        "location",
        "message",
        "repair_boundary",
    }
    extra = set(blocker) - required
    missing = required - set(blocker)
    errors: list[str] = []
    if missing:
        errors.append(
            f"{context} blocker is missing fields: {sorted(missing)}"
        )
    if extra:
        errors.append(
            f"{context} blocker contains unsupported fields: {sorted(extra)}"
        )
    for field in sorted(required):
        if not isinstance(blocker.get(field), str) or not str(
            blocker.get(field) or ""
        ).strip():
            errors.append(f"{context} blocker.{field} must be a non-empty string")
    return errors


def _minimal_owner_report_errors(
    report: dict[str, Any],
    *,
    context: str,
    terminal_statuses: set[str],
) -> list[str]:
    """Validate the current minimal owner report."""

    status = str(report.get("status") or "")
    errors: list[str] = []
    allowed = {"status"}
    if status == "blocked":
        allowed.add("blocker")
    extra = set(report) - allowed
    if extra:
        errors.append(
            f"{context} report contains unsupported fields: {sorted(extra)}"
        )
    if status not in terminal_statuses:
        errors.append(
            f"{context} report status must be "
            + ", ".join(sorted(terminal_statuses))
        )
    if status == "blocked":
        errors.extend(_blocker_contract_errors(report.get("blocker"), context=context))
        blocker = report.get("blocker")
        if context == "vc-checking" and isinstance(blocker, dict):
            failure_class = blocker.get("failure_class")
            if (
                isinstance(failure_class, str)
                and failure_class
                and failure_class not in VC_CHECKING_BLOCKER_RETRY_PHASES
            ):
                errors.append(
                    "vc-checking blocker.failure_class must be one of: "
                    + ", ".join(sorted(VC_CHECKING_BLOCKER_RETRY_PHASES))
                )
    elif "blocker" in report:
        errors.append(f"{context} non-blocked result cannot contain blocker")
    return errors


def _next_annotation_causal_retry_count(
    previous: dict[str, Any], feedback_payloads: list[dict[str, Any]]
) -> int:
    """Count only feedback whose machine class requires annotation repair."""

    failure_classes = [
        str(blocker["failure_class"])
        for payload in feedback_payloads
        if isinstance(payload, dict)
        and isinstance((blocker := payload.get("blocker")), dict)
        and isinstance(blocker.get("failure_class"), str)
    ]
    count = int(previous.get("annotation_causal_retry_count", 0))
    if failure_classes and all(
        item in ANNOTATION_CAUSAL_FAILURE_CLASSES for item in failure_classes
    ):
        return count + 1
    if feedback_payloads and all(
        isinstance(payload, dict) and payload.get("status") == "compact-error"
        for payload in feedback_payloads
    ):
        return count
    return 0


def _refresh_group_worker_input(
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    group: dict[str, Any],
) -> Path:
    """Render the current worker contract before every future delivery.

    Group directories can remain prepared across a controller upgrade.  The
    handoff is controller-owned rather than acceptance evidence, so refreshing
    it at claim time gives an older prepared group the current concise rules
    without changing either sealed formal file.
    """

    group_state = proving.get("groups", {}).get(group_id)
    if not isinstance(group_state, dict):
        raise SystemExit(f"group state missing while rendering handoff: {group_id}")
    report_dir = fixed_path_under(
        Path(str(group["report_directory"])),
        Path(str(state["report_root"])),
        label="group report directory",
    )
    input_path = fixed_path_under(
        report_dir / "group_worker_input.md",
        report_dir,
        label="group worker input",
    )
    repair_index = (
        int(group_state.get("repair_index", 0))
        if group_state.get("status") == "repair-prepared"
        else 0
    )
    feedback = group_state.get("repair_feedback")
    repair_feedback = (
        (
            f"Category: {feedback.get('category') or 'group-check'}\n"
            f"Failure: {feedback.get('message') or 'group repair is required'}\n"
            f"Required repair: {feedback.get('repair') or 'Rerun the exact controller check after repairing only authorized files.'}"
        )
        if repair_index and isinstance(feedback, dict)
        else None
    )
    commands = group_worker_commands(
        main_root=Path(str(state["main_root"])),
        run_root=Path(str(state["run_root"])),
        round_id=str(proving["round"]),
        group_id=group_id,
        group_directory=Path(str(group["directory"])),
    )
    write_text(
        input_path,
        render_group_worker_input(
            group,
            formal_case_lib=(
                str(state["target_files"]["formal_case_lib"])
                if group.get("group_worker_lib")
                else None
            ),
            report_dir=report_dir,
            commands=commands,
            attempt_index=int(group_state.get("attempt_index", 1)),
            previous_compact_attempts=len(group_state.get("compact_attempts", [])),
            repair_index=repair_index,
            repair_feedback=repair_feedback,
        ),
    )
    return input_path


def _attempt_artifact(
    state: dict[str, Any], attempt: dict[str, Any], key: str
) -> Path:
    try:
        paths = _validated_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        raise SystemExit(
            f"{attempt.get('phase', 'phase')} attempt path topology is invalid: {exc}"
        ) from exc
    if key not in paths:
        raise SystemExit(f"unsupported attempt artifact role: {key}")
    return paths[key]


def _annotation_after_drift_errors(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    main_root = Path(str(state["main_root"]))
    after_root = Path(str(attempt["annotation_history_directory"])) / "after"
    snapshot_errors = _annotation_after_snapshot_errors(state, attempt)
    if snapshot_errors:
        # The archived copy is provenance, not a second mutable source of
        # truth. Never compare current files against it until its own seal has
        # been revalidated; matching edits to both trees must not hide drift.
        return snapshot_errors
    if not after_root.is_dir():
        return ["annotation finalized after-history snapshot is missing"]
    relatives = [
        str(state["target_files"][key])
        for key in (
            "c_file",
            "formal_case_lib",
            "goal_file",
            "proof_auto_file",
            "proof_manual_file",
            "goal_check_file",
        )
    ]
    try:
        current = _snapshot_digests(main_root, relatives)
        archived = _snapshot_digests(after_root, relatives)
    except (OSError, ValueError) as exc:
        return [f"current annotation topology cannot be compared safely: {exc}"]
    return [
        f"current annotation file changed after finalize-delivery: {relative}"
        for relative in relatives
        if current[relative] != archived[relative]
    ]


def _fixed_artifact_paths(
    paths: dict[str, Path], *, main_root: Path
) -> dict[str, Path]:
    return {
        key: fixed_path_under(path, main_root, label=f"returned {key} artifact")
        for key, path in paths.items()
    }


def _artifact_digests(paths: dict[str, Path], *, main_root: Path) -> dict[str, str]:
    paths = _fixed_artifact_paths(paths, main_root=main_root)
    missing = [str(path) for path in paths.values() if not path.is_file()]
    if missing:
        raise SystemExit(
            "returned attempt artifacts are missing: " + ", ".join(missing)
        )
    return {key: _file_digest(path) for key, path in paths.items()}


def _group_formal_artifact_paths(group: dict[str, Any]) -> dict[str, Path]:
    paths = {"proof_manual": Path(str(group["proof_manual"]))}
    group_worker_lib = group.get("group_worker_lib")
    if isinstance(group_worker_lib, str) and group_worker_lib:
        paths["group_worker_lib"] = Path(group_worker_lib)
    return paths


def _artifact_integrity_errors(
    paths: dict[str, Path], expected: dict[str, str] | None, *, main_root: Path
) -> list[str]:
    if not isinstance(expected, dict):
        return ["returned attempt artifacts were not sealed"]
    try:
        paths = _fixed_artifact_paths(paths, main_root=main_root)
    except SystemExit as exc:
        return [str(exc)]
    errors: list[str] = []
    for key, path in paths.items():
        if not path.is_file():
            errors.append(f"sealed {key} artifact is missing: {path}")
        elif _file_digest(path) != expected.get(key):
            errors.append(f"sealed {key} artifact changed after return: {path}")
    return errors


def _repair_formal_integrity_errors(
    group_state: dict[str, Any], group: dict[str, Any], *, main_root: Path
) -> list[str]:
    """Keep report-only repair from reopening already sealed formal bytes."""

    expected = group_state.get("repair_formal_sha256")
    if not isinstance(expected, dict):
        return []
    paths = _group_formal_artifact_paths(group)
    unexpected = set(expected) - set(paths)
    if unexpected:
        return [
            "report-only repair seal names absent formal artifacts: "
            + ", ".join(sorted(unexpected))
        ]
    try:
        paths = _fixed_artifact_paths(paths, main_root=main_root)
    except SystemExit as exc:
        return [str(exc)]
    errors: list[str] = []
    for key, path in paths.items():
        if not path.is_file() or _file_digest(path) != expected.get(key):
            errors.append(f"report-only repair changed sealed {key}: {path}")
    return errors


def _terminate_report_only_repair_after_formal_drift(
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    message: str,
) -> None:
    """Make a violated report-only repair terminal instead of leaving it queued.

    A report-contract retry deliberately reopens only the compact JSON report
    (and optional human notes).  The copied manual and group-worker library are
    sealed at preparation time.  Merely raising on a later mismatch would
    strand either the queued append action or an already-running delivery: the
    next invocation would observe the same mismatch forever.  Commit one
    explicit terminal transition, close any live timing interval, and let the
    normal scheduler publish the compact artifact-drift blocker.
    """

    group_state = proving["groups"][group_id]
    stopped_at = _utc()
    interval_index = int(group_state.get("timing_interval_index", -1))
    intervals = proving.setdefault("timing", {}).setdefault("group-work", [])
    if 0 <= interval_index < len(intervals) and not intervals[interval_index].get(
        "finished_at"
    ):
        intervals[interval_index]["finished_at"] = stopped_at
        intervals[interval_index]["elapsed_seconds"] = _elapsed_between(
            str(intervals[interval_index]["started_at"]), stopped_at
        )

    blocker = {
        "failure_class": "invalid-report",
        "round": str(proving["round"]),
        "group_id": group_id,
        "message": str(message),
        "sealed_artifact_drift": True,
    }
    group_state["status"] = "invalid-report"
    group_state["validation_errors"] = [str(message)]
    group_state["blockers"] = [blocker]
    group_state["repair_terminated_at"] = stopped_at
    for key in (
        "delivery",
        "repair_feedback",
        "repair_formal_sha256",
        "timing_interval_index",
    ):
        group_state.pop(key, None)
    # A formal edit during a report-only retry is not a failed-but-structured
    # proof candidate.  Discard any provisional reuse seal and route through
    # the invalid-report blocker without reopening this worker.
    proving.pop("reuse_group_artifacts", None)
    _sync_group_actions(state, proving)


def _annotation_report_contract_errors(
    report: dict[str, Any],
    *,
    expected_changed_files: list[str],
    allowed_write_paths: list[str],
) -> list[str]:
    """One mechanical report contract shared by preflight and validation."""

    errors = _minimal_owner_report_errors(
        report,
        context="annotation",
        terminal_statuses=ANNOTATION_TERMINAL_STATUSES,
    )
    if not set(expected_changed_files) <= set(allowed_write_paths):
        errors.append("annotation changed paths outside allowed_write_paths")
    return errors


def _group_report_contract_errors(
    report: dict[str, Any],
    *,
    state: dict[str, Any],
    group_state: dict[str, Any],
    formal_digests: dict[str, str],
    version_errors: list[str],
) -> list[str]:
    """Validate an owner outcome; controller validates all machine facts."""

    del state, group_state, formal_digests
    errors = _minimal_owner_report_errors(
        report,
        context="group",
        terminal_statuses=GROUP_TERMINAL_STATUSES,
    )
    status = str(report.get("status") or "")
    if status == "completed" and version_errors:
        errors.append(
            "completed group cannot be finalized after current source-version drift"
        )
    return errors


def _queue_annotation_feedback(
    state: dict[str, Any], source_attempt: str, reason: str
) -> None:
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


def _sealed_vc_checking_blocker(
    state: dict[str, Any], attempt: dict[str, Any]
) -> dict[str, Any] | None:
    """Return a blocker only when its fixed owner report still matches its seal."""

    if attempt.get("phase") != "vc-checking":
        return None
    try:
        report_path = _attempt_artifact(state, attempt, "report")
        integrity_errors = _artifact_integrity_errors(
            {"report": report_path},
            attempt.get("artifact_sha256"),
            main_root=Path(str(state["main_root"])),
        )
        if integrity_errors:
            return None
        payload = _json_load(report_path, {})
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, SystemExit):
        return None
    if payload.get("status") != "blocked":
        return None
    blocker = payload.get("blocker")
    return blocker if isinstance(blocker, dict) else None


def _normalized_infrastructure_blocker_identity(
    attempt: dict[str, Any], blocker: dict[str, Any]
) -> tuple[str, str, str] | None:
    """Normalize the round-specific part of an infrastructure topology failure."""

    if blocker.get("failure_class") != "infrastructure":
        return None
    kind = str(blocker.get("kind") or "").strip()
    location = str(blocker.get("location") or "").strip().replace("\\", "/")
    round_id = str(attempt.get("round") or "").strip().replace("\\", "/")
    if not kind or not location or not round_id:
        return None
    return (
        "infrastructure",
        kind,
        location.replace(round_id, "<vc-checking-round>"),
    )


def _identical_infrastructure_blocker_chain(
    state: dict[str, Any],
    attempt: dict[str, Any],
    blocker: dict[str, Any],
) -> tuple[tuple[str, str, str] | None, list[str]]:
    """Find the consecutive same-version VC attempts with one topology failure."""

    identity = _normalized_infrastructure_blocker_identity(attempt, blocker)
    if identity is None:
        return None, []
    current_attempt_id = str(attempt.get("attempt_id") or "")
    current_source = str(attempt.get("source_version") or "")
    current_goals = str(attempt.get("source_goal_version") or "")
    vc_attempts = [
        item
        for item in state.get("attempts", {}).values()
        if isinstance(item, dict) and item.get("phase") == "vc-checking"
    ]
    try:
        current_index = next(
            index
            for index, item in enumerate(vc_attempts)
            if item.get("attempt_id") == current_attempt_id
        )
    except StopIteration:
        return identity, []
    matching: list[str] = []
    for candidate in reversed(vc_attempts[: current_index + 1]):
        if (
            str(candidate.get("source_version") or "") != current_source
            or str(candidate.get("source_goal_version") or "") != current_goals
        ):
            break
        candidate_blocker = (
            blocker
            if candidate.get("attempt_id") == current_attempt_id
            else _sealed_vc_checking_blocker(state, candidate)
        )
        if (
            not isinstance(candidate_blocker, dict)
            or _normalized_infrastructure_blocker_identity(
                candidate, candidate_blocker
            )
            != identity
        ):
            break
        matching.append(str(candidate["attempt_id"]))
    matching.reverse()
    return identity, matching


def _queue_vc_checking_retry(
    state: dict[str, Any],
    attempt: dict[str, Any],
    reason: str,
    *,
    compact: bool = False,
    blocker: dict[str, Any] | None = None,
) -> None:
    """Publish the one reusable same-phase vc-checking retry shape."""

    if reason == "vc-checking-infrastructure" and isinstance(blocker, dict):
        identity, matching_attempts = _identical_infrastructure_blocker_chain(
            state,
            attempt,
            blocker,
        )
        if (
            identity is not None
            and len(matching_attempts) >= MAX_IDENTICAL_INFRASTRUCTURE_BLOCKERS
        ):
            failure_class, kind, normalized_location = identity
            state["next_actions"] = []
            state["current_blockers"] = [
                {
                    "failure_class": failure_class,
                    "kind": "repeated-vc-checking-infrastructure-blocker",
                    "repeated_kind": kind,
                    "normalized_location": normalized_location,
                    "repeat_count": len(matching_attempts),
                    "attempts": matching_attempts,
                    "message": (
                        "The same VC-checking infrastructure topology failure "
                        "repeated without a controller configuration change."
                    ),
                    "repair_boundary": (
                        "Repair the controller/handoff infrastructure, then "
                        "resume from the preserved VC-checking phase."
                    ),
                }
            ]
            return

    state["next_actions"] = [
        {
            "id": (
                f"vc-checking-compact-retry-{attempt['round']}"
                if compact
                else f"vc-checking-retry-{attempt['round']}"
            ),
            "kind": "main-owned-action",
            "action": "retry-round",
            "phase": "vc-checking",
            "reason": reason,
            "previous_attempt": attempt["attempt_id"],
        }
    ]


def _transition_current_version_drift(
    state: dict[str, Any],
    attempt: dict[str, Any],
    *,
    action: str,
    feedback_attempt_id: str,
    retry_reason: str | None = None,
) -> list[str]:
    """Turn a main-owned version gate failure into annotation feedback.

    A plain exception leaves the same impossible action queued forever. This
    transition preserves only the first mechanical mismatch, marks the
    downstream attempt stale, and uses the existing persistent annotation
    retry path. ``feedback_attempt_id`` must name sealed owner artifacts (for a
    proving round this is its accepted vc-checking source, not the proving
    attempt, which has no phase-agent report).
    """

    errors = _current_version_errors(state)
    if not errors:
        return []
    previous_status = str(attempt.get("status") or "")
    attempt["status"] = "stale"
    attempt["stale_from_status"] = previous_status
    attempt["stale_reason"] = errors[0]
    attempt.setdefault("finished_at", _utc())
    receipt = {
        "failure_class": "current-version-drift",
        "action": action,
        "message": errors[0],
        "error_count": len(errors),
        "detected_at": _utc(),
    }
    attempt["version_drift"] = receipt
    state["current_blockers"] = [receipt]
    _queue_annotation_feedback(
        state,
        feedback_attempt_id,
        retry_reason or f"{attempt.get('phase', 'downstream')}-stale",
    )
    return errors


def _proving_manifest_errors(
    state: dict[str, Any], proving: dict[str, Any]
) -> list[str]:
    try:
        paths = _validated_proving_attempt_paths(state, proving)
    except (OSError, ValueError) as exc:
        return [f"vc-proving attempt path topology is invalid: {exc}"]
    errors: list[str] = []
    for path_field, digest_field, label in (
        ("base_manifest", "base_manifest_sha256", "base_manifest"),
        (
            "group_workers_manifest",
            "group_workers_manifest_sha256",
            "group_workers_manifest",
        ),
    ):
        path = paths[path_field]
        expected = str(proving.get(digest_field) or "")
        if not path.is_file() or not expected:
            errors.append(f"{label} integrity record is missing")
        elif _file_digest(path) != expected:
            errors.append(f"{label} changed after vc-proving preparation")
    return errors


def _resolved_proving_manifest(
    state: dict[str, Any], proving: dict[str, Any]
) -> dict[str, Any]:
    paths = _validated_proving_attempt_paths(state, proving)
    return resolve_group_workers_manifest(
        paths["group_workers_manifest"],
        main_root=Path(str(state["main_root"])),
        expected_run_root=paths["directory"].parent,
        expected_round=str(proving["round"]),
    )


def _public_helper_pool_errors(state: dict[str, Any]) -> list[str]:
    record = state.get("public_helper_lemma_lib")
    if not isinstance(record, dict):
        return ["controller state has no public helper candidate pool record"]
    run_root = Path(str(state["run_root"]))
    expected_path = public_helper_lemma_lib_path(run_root)
    try:
        recorded_path = fixed_path_under(
            Path(str(record.get("path") or "")),
            run_root,
            label="recorded public helper candidate pool",
        )
    except SystemExit as exc:
        return [str(exc)]
    if recorded_path != expected_path:
        return ["public helper candidate pool path is not the fixed run-root path"]
    try:
        snapshot = public_helper_pool_snapshot(expected_path)
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        return [f"public helper candidate pool is invalid: {exc}"]
    mismatched = [
        field
        for field in ("sha256", "declaration_count", "helper_count")
        if record.get(field) != snapshot.get(field)
    ]
    pending = state.get("public_helper_promotion_transaction")
    if mismatched:
        # A process may die after the atomic pool replacement but before the
        # group-acceptance state commit.  Only the exact before->after receipt
        # written ahead of that replacement can reconcile the bytes.
        if (
            isinstance(pending, dict)
            and record.get("sha256") == pending.get("before_sha256")
            and snapshot.get("sha256") == pending.get("after_sha256")
        ):
            state["public_helper_lemma_lib"] = {
                key: snapshot[key]
                for key in ("path", "sha256", "declaration_count", "helper_count")
            }
            pending["status"] = "applied"
            return []
        return ["public helper candidate pool changed outside controller append"]
    if isinstance(pending, dict) and snapshot.get("sha256") == pending.get(
        "after_sha256"
    ):
        pending["status"] = "applied"
    return []


def _refresh_public_helper_pool_state(state: dict[str, Any]) -> None:
    snapshot = public_helper_pool_snapshot(
        public_helper_lemma_lib_path(Path(str(state["run_root"])))
    )
    state["public_helper_lemma_lib"] = {
        key: snapshot[key]
        for key in ("path", "sha256", "declaration_count", "helper_count")
    }


def _group_assignment_projection(group: dict[str, Any]) -> dict[str, Any]:
    """Project the accepted-plan fields shared by plan and worker manifest."""

    witnesses: list[dict[str, Any]] = []
    raw_witnesses = group.get("witnesses")
    if isinstance(raw_witnesses, list):
        for witness in raw_witnesses:
            if not isinstance(witness, dict):
                witnesses.append({"invalid": str(witness)})
                continue
            split_goals: list[dict[str, str]] = []
            raw_split_goals = witness.get("split_goals")
            if isinstance(raw_split_goals, list):
                for split_goal in raw_split_goals:
                    if not isinstance(split_goal, dict):
                        split_goals.append({"invalid": str(split_goal)})
                        continue
                    item = {"name": str(split_goal.get("name") or "")}
                    if "strategy" in split_goal:
                        item["strategy"] = str(split_goal.get("strategy") or "")
                    split_goals.append(item)
            projected_witness = {
                "name": str(witness.get("name") or ""),
                "proof_mode": str(witness.get("proof_mode") or ""),
                "split_goals": split_goals,
            }
            if "strategy" in witness:
                projected_witness["strategy"] = str(
                    witness.get("strategy") or ""
                )
            witnesses.append(projected_witness)
    return {
        "id": str(group.get("id") or ""),
        "estimated_difficulty": group.get("estimated_difficulty"),
        "witnesses": witnesses,
        "helpers": [
            {
                "name": str(item.get("name") or ""),
                "strategy": str(item.get("strategy") or ""),
                "visibility": str(item.get("visibility") or ""),
            }
            if isinstance(item, dict)
            else {"invalid": str(item)}
            for item in group.get("helpers", [])
        ],
    }


def _accepted_plan_manifest_errors(
    state: dict[str, Any], proving: dict[str, Any], manifest: dict[str, Any]
) -> list[str]:
    accepted = state.get("accepted_rounds", {}).get("vc-checking")
    if not isinstance(accepted, dict):
        return ["vc-proving group check has no accepted vc-checking plan"]
    accepted_attempt_id = accepted.get("attempt_id")
    if accepted_attempt_id is None:
        expected_plan = Path(str(state["report_root"])) / "group_plan.json"
    else:
        accepted_attempt = state.get("attempts", {}).get(str(accepted_attempt_id))
        if not isinstance(accepted_attempt, dict):
            return ["accepted vc-checking attempt is missing"]
        try:
            expected_plan = _validated_attempt_paths(
                state, accepted_attempt
            )["group_plan"]
        except (OSError, ValueError) as exc:
            return [f"accepted vc-checking attempt path topology is invalid: {exc}"]
    plan_path = Path(str(accepted.get("group_plan") or ""))
    if plan_path != expected_plan:
        return ["accepted group_plan.json path differs from current run topology"]
    plan_digest = str(accepted.get("group_plan_sha256") or "")
    if (
        not plan_path.is_file()
        or not plan_digest
        or _file_digest(plan_path) != plan_digest
    ):
        return ["accepted group_plan.json changed after vc-proving preparation"]
    plan = _json_load(plan_path, {})
    current_goal = str(state.get("source_goal_version", {}).get("digest") or "")
    if proving.get("source_goal_version") != current_goal:
        return ["accepted group plan or vc-proving source_goal_version is stale"]
    targets = [
        str(item)
        for item in state.get("source_goal_version", {}).get(
            "target_witnesses", []
        )
    ]
    synthetic_lemmas = [
        {"name": declaration}
        for witness in targets
        for declaration in [
            *[
                str(item["name"])
                for item in state["source_goal_version"]
                .get("split_goals", {})
                .get(witness, [])
            ],
            witness,
        ]
    ]
    try:
        plan_entries = group_entries_from_plan(synthetic_lemmas, plan)
    except (KeyError, TypeError, ValueError, SystemExit) as exc:
        return [f"accepted group plan is invalid: {exc}"]
    plan_groups = [
        {
            "id": entry["group_id"],
            "estimated_difficulty": entry["estimated_difficulty"],
            "witnesses": [
                {
                    "name": witness["name"],
                    "proof_mode": witness["proof_mode"],
                    **(
                        {"strategy": witness["strategy"]}
                        if "strategy" in witness
                        else {}
                    ),
                    "split_goals": [
                        {
                            "name": split_goal["name"],
                            **(
                                {"strategy": split_goal["strategy"]}
                                if split_goal.get("strategy")
                                else {}
                            ),
                        }
                        for split_goal in witness["split_goals"]
                    ],
                }
                for witness in entry["witnesses"]
            ],
            "helpers": [dict(helper) for helper in entry["planned_helpers"]],
        }
        for entry in plan_entries
    ]
    manifest_groups = (
        manifest.get("groups") if isinstance(manifest.get("groups"), list) else []
    )
    plan_projection = [
        _group_assignment_projection(item)
        for item in plan_groups
        if isinstance(item, dict)
    ]
    manifest_projection = [
        _group_assignment_projection(item)
        for item in manifest_groups
        if isinstance(item, dict)
    ]
    if plan_projection != manifest_projection:
        mismatch = next(
            (
                index
                for index, (planned, prepared) in enumerate(
                    zip(plan_projection, manifest_projection, strict=False)
                )
                if planned != prepared
            ),
            min(len(plan_projection), len(manifest_projection)),
        )
        group_id = (
            plan_projection[mismatch]["id"]
            if mismatch < len(plan_projection)
            else manifest_projection[mismatch]["id"]
            if mismatch < len(manifest_projection)
            else "unknown"
        )
        return [
            f"worker manifest assignment for group `{group_id}` does not match the accepted group plan"
        ]
    return []


def _group_failure_details(message: str, *, recoverable: bool) -> dict[str, Any]:
    lowered = message.lower()
    if any(
        marker in lowered
        for marker in (
            "proof mode",
            "llm_pre_process",
            "aggressive_pre_process",
        )
    ):
        category = "route"
        repair = (
            "Keep the controller-selected proof mode; for an aggressive route, prove every assigned split goal "
            "first, use aggressive_pre_process, and close its resulting branches with Goal_apply on the corresponding "
            "split lemmas. For an LLM_pre_process route, restore every generated split block exactly and prove only "
            "the top-level VC."
        )
    elif any(
        marker in lowered
        for marker in ("admitted/abort", "contains admitted", "incomplete proof")
    ):
        category = "proof-completeness"
        repair = (
            "Close every assigned top-level proof and aggressive split proof with Qed/Defined; retain Abort only in "
            "the protected split blocks of an LLM_pre_process witness."
        )
    elif any(
        marker in lowered
        for marker in (
            "group report",
            "report status",
            "report blockers",
            "completed group cannot",
            "blocked group must",
            "stale group status",
        )
    ):
        category = "report-contract"
        repair = (
            "Correct group_worker_report.json in the same fixed report directory. A completed result has only the "
            "current status fields; a blocked result also has one complete blocker. Optional notes may change, but "
            "the sealed copied manual and worker library must not. Then finalize the same worker delivery."
        )
    elif any(
        marker in lowered
        for marker in (
            "forbidden",
            "unsafe",
            "axiom",
            "helper namespace",
            "official import",
            "extra top-level command",
        )
    ):
        category = "safety"
        repair = (
            "Remove the forbidden construct; keep every new or adapted helper inside this group's suffix namespace. "
            "Only a token-identical sealed public/reuse helper may retain its source suffix, and imports must remain "
            "permitted official imports."
        )
    elif any(
        marker in lowered
        for marker in (
            "manifest",
            "group_plan",
            "source_goal_version",
            "source_version",
            "stale",
            "fixed group directory",
            "report directory",
            "missing group_worker",
        )
    ):
        category = "contract"
        repair = (
            "Do not edit controller-owned inputs or fixed paths. Return this failure to "
            "the main controller transition unless the message names an owner-editable report field."
        )
    else:
        category = "structure"
        repair = (
            "Restore protected declaration/proof tokens, ownership, and route; change only assigned proof spans "
            "and permitted suffixed helper declarations. Formatting-only comments, whitespace, and line endings "
            "do not need repair."
        )
    return {
        "category": category,
        "kind": f"group-{category}",
        "message": message,
        "repair": repair,
        "recoverable": recoverable,
    }


def _group_structure_validation(
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    *,
    require_complete: bool = True,
) -> dict[str, Any]:
    """Run the shared pre-Coq structure check used by worker and controller."""

    fatal_errors = [
        *_proving_manifest_errors(state, proving),
        *_current_version_errors(state),
    ]
    # Current-round workers consume only the immutable
    # public_helper_snapshot.txt pinned in their manifest. The durable pool is
    # intentionally append-only for future rounds, so sibling validation may
    # legally advance it while this exact check is running. Pool integrity is
    # checked at preparation, promotion, parent verify,
    # and finalization instead of coupling this round to live mutable state.
    manifest: dict[str, Any] = {}
    group: dict[str, Any] | None = None
    if not fatal_errors:
        try:
            manifest = _resolved_proving_manifest(state, proving)
            if not isinstance(manifest, dict):
                fatal_errors.append("current group_workers_manifest is invalid")
            else:
                fatal_errors.extend(
                    _accepted_plan_manifest_errors(state, proving, manifest)
                )
        except (OSError, json.JSONDecodeError, UnicodeDecodeError) as exc:
            fatal_errors.append(f"group structure inputs cannot be read: {exc}")
    if not fatal_errors:
        group = next(
            (
                item
                for item in manifest.get("groups", [])
                if isinstance(item, dict) and str(item.get("id")) == group_id
            ),
            None,
        )
        if group is None:
            fatal_errors.append(f"group `{group_id}` is missing from current manifest")
    if fatal_errors:
        failure = _group_failure_details(str(fatal_errors[0]), recoverable=False)
        return {
            "errors": fatal_errors,
            "recoverable": False,
            "first_failure": failure,
            "group": group,
        }
    try:
        candidate = validate_group_for_acceptance_result(
            Path(str(proving["group_workers_manifest"])),
            group_id=group_id,
            main_root=Path(str(state["main_root"])),
            expected_proof_manual=str(state["target_files"]["proof_manual_file"]),
            expected_formal_case_lib=str(state["target_files"]["formal_case_lib"]),
            require_complete=require_complete,
            expected_run_root=Path(str(state["run_root"])),
            expected_round=str(proving["round"]),
            forbidden_modules=_generated_artifact_module_spellings_for_state(
                state,
                source_goal_version=state["source_goal_version"],
            ),
        )
    except (
        OSError,
        ValueError,
        json.JSONDecodeError,
        UnicodeDecodeError,
        SystemExit,
    ) as exc:
        message = f"group candidate validation failed: {exc}"
        return {
            "errors": [message],
            "recoverable": False,
            "first_failure": _group_failure_details(message, recoverable=False),
            "group": group,
        }
    errors = [str(item) for item in candidate["errors"]]
    recoverable = bool(candidate.get("recoverable"))
    return {
        "errors": errors,
        "recoverable": recoverable,
        "first_failure": (
            _group_failure_details(errors[0], recoverable=recoverable)
            if errors
            else None
        ),
        "group": group,
    }


def _find_round_attempt(
    state: dict[str, Any], identifier: str
) -> dict[str, Any] | None:
    if (
        identifier in state["attempts"]
        and state["attempts"][identifier].get("phase") != VC_PROVING_PHASE
    ):
        attempt = state["attempts"][identifier]
        _validated_attempt_paths(state, attempt)
        return attempt
    recorded = Path(identifier).expanduser()
    path = Path(os.path.abspath(os.fspath(recorded)))
    if not recorded.is_absolute() or recorded != path:
        return None
    for attempt in reversed(list(state["attempts"].values())):
        if attempt.get("phase") == VC_PROVING_PHASE:
            continue
        paths = _validated_attempt_paths(state, attempt)
        candidates = {paths["directory"], paths["report"]}
        if path in candidates:
            return attempt
    return None


def _find_group_attempt(
    state: dict[str, Any], identifier: str
) -> tuple[dict[str, Any], str] | None:
    if ":" in identifier:
        round_id, group_id = identifier.split(":", 1)
        attempt = state["attempts"].get(round_id)
        if (
            attempt
            and attempt.get("phase") == VC_PROVING_PHASE
            and group_id in attempt.get("groups", {})
        ):
            return attempt, group_id
    recorded = Path(identifier).expanduser()
    path = Path(os.path.abspath(os.fspath(recorded)))
    if not recorded.is_absolute() or recorded != path:
        return None
    for attempt in state["attempts"].values():
        if attempt.get("phase") != VC_PROVING_PHASE:
            continue
        manifest = _resolved_proving_manifest(state, attempt)
        for group in manifest.get("groups", []) if isinstance(manifest, dict) else []:
            report = (
                Path(str(group.get("report_directory", ""))).resolve()
                / "group_worker_report.json"
            )
            if path in {report, report.parent}:
                return attempt, str(group["id"])
    return None


def _claimed_delivery(
    state: dict[str, Any], action_id: str
) -> tuple[dict[str, Any], str] | None:
    for attempt in state.get("attempts", {}).values():
        delivery = attempt.get("delivery")
        if isinstance(delivery, dict) and delivery.get("action_id") == action_id:
            return delivery, str(attempt["attempt_id"])
        for group_id, group_state in (attempt.get("groups") or {}).items():
            delivery = (
                group_state.get("delivery") if isinstance(group_state, dict) else None
            )
            if isinstance(delivery, dict) and delivery.get("action_id") == action_id:
                return delivery, f"{attempt['round']}:{group_id}"
    return None


def _claimed_delivery_action(
    state: dict[str, Any], delivery: dict[str, Any], attempt_id: str
) -> dict[str, Any]:
    """Rebuild a claimed action from authoritative attempt/manifest state."""

    kind = str(delivery["kind"])
    action: dict[str, Any] = {
        "id": str(delivery["action_id"]),
        "kind": kind,
        "attempt_id": attempt_id,
    }
    attempt = _find_round_attempt(state, attempt_id)
    if attempt is not None:
        action.update(
            {
                "phase": str(attempt["phase"]),
                "input": str(attempt["input"]),
                "report": str(attempt["report"]),
            }
        )
        if kind in {"spawn-annotation-agent", "append-annotation-agent"}:
            session = state.get("annotation_session")
            if not isinstance(session, dict) or not session.get("session_id"):
                raise SystemExit(
                    "claimed annotation delivery has no persistent session"
                )
            action.update(
                {
                    "session_id": str(session["session_id"]),
                    "feedback_sources": attempt.get("feedback_sources", []),
                    "consider_broader_refactor": _consider_broader_refactor(
                        attempt
                    ),
                }
            )
        return action

    found = _find_group_attempt(state, attempt_id)
    if found is None:
        raise SystemExit(f"claimed delivery attempt no longer exists: {attempt_id}")
    proving, group_id = found
    integrity_errors = _proving_manifest_errors(state, proving)
    if integrity_errors:
        raise SystemExit(
            "claimed group delivery manifest failed integrity: " + integrity_errors[0]
        )
    manifest = _resolved_proving_manifest(state, proving)
    group = next(
        (
            item
            for item in manifest.get("groups", [])
            if str(item.get("id")) == group_id
        ),
        None,
    )
    if not isinstance(group, dict):
        raise SystemExit(f"claimed group no longer exists in manifest: {group_id}")
    report_directory = Path(str(group["report_directory"]))
    action.update(
        {
            "phase": VC_PROVING_PHASE,
            "round": str(proving["round"]),
            "group_id": group_id,
            "input": str(report_directory / "group_worker_input.md"),
            "report": str(report_directory / "group_worker_report.json"),
        }
    )
    return action


def _bind_delivery_owner(
    state: dict[str, Any],
    owner_record: dict[str, Any],
    owner: str,
    *,
    annotation: bool = False,
) -> None:
    existing = str(owner_record.get("owner") or "")
    if existing and existing != owner:
        raise SystemExit(
            f"attempt is already bound to owner `{existing}`; duplicate owner `{owner}` is refused"
        )
    owner_record["owner"] = owner
    if annotation:
        session = state.get("annotation_session")
        if not isinstance(session, dict):
            raise SystemExit("annotation delivery has no persistent session")
        session_owner = str(session.get("owner") or "")
        if session_owner and session_owner != owner:
            raise SystemExit(
                f"annotation session is already bound to owner `{session_owner}`"
            )
        session["owner"] = owner


def claim_attempt(args: argparse.Namespace) -> int:
    """Atomically claim one agent action, bind its owner, and start timing."""

    owner = str(args.owner).strip()
    if not owner:
        raise SystemExit("--owner must be a non-empty stable agent owner")
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    action = next(
        (
            item
            for item in state.get("next_actions", [])
            if item.get("id") == args.next_action
        ),
        None,
    )
    if action is None:
        claimed = _claimed_delivery(state, args.next_action)
        if claimed is None:
            raise SystemExit(f"agent delivery action not found: {args.next_action}")
        delivery, attempt_id = claimed
        if delivery.get("owner") != owner:
            raise SystemExit(
                f"delivery was claimed by owner `{delivery.get('owner')}`; duplicate owner `{owner}` is refused"
            )
        claimed_attempt = _find_round_attempt(state, attempt_id)
        if (
            isinstance(claimed_attempt, dict)
            and claimed_attempt.get("phase") == "annotation"
        ):
            feedback_errors = _feedback_source_reference_errors(
                state, claimed_attempt
            )
            if feedback_errors:
                raise SystemExit(
                    "annotation feedback source changed before repeated handoff: "
                    + feedback_errors[0]
                )
        claimed_action = _claimed_delivery_action(state, delivery, attempt_id)
        message = _delivery_message(claimed_action)
        print(
            json.dumps(
                {
                    "status": "already-claimed",
                    "attempt": attempt_id,
                    "owner": owner,
                    "message": message,
                    "handoff": handoff_payload(
                        state, claimed_action, message, owner=owner
                    ),
                    "finalize_invocation": finalize_invocation(
                        state, attempt_id, owner
                    ),
                },
                indent=2,
            )
        )
        return 0
    if action.get("kind") not in DELIVERY_ACTION_KINDS:
        raise SystemExit(f"action is not an agent delivery: {args.next_action}")
    if action.get("kind") in {"spawn-group-worker", "append-group-worker"}:
        found = _find_group_attempt(state, str(action.get("attempt_id") or ""))
        if found is None:
            raise SystemExit("group delivery no longer belongs to a current attempt")
        proving_for_claim, group_id_for_claim = found
        integrity_errors = _proving_manifest_errors(state, proving_for_claim)
        if integrity_errors:
            raise SystemExit(
                "group delivery manifest failed integrity before claim: "
                + integrity_errors[0]
            )
        manifest_for_claim = _resolved_proving_manifest(state, proving_for_claim)
        group_for_claim = next(
            (
                item
                for item in manifest_for_claim.get("groups", [])
                if isinstance(item, dict) and str(item.get("id")) == group_id_for_claim
            ),
            None,
        )
        if not isinstance(group_for_claim, dict):
            raise SystemExit("group delivery assignment disappeared before claim")
        repair_errors = _repair_formal_integrity_errors(
            proving_for_claim["groups"][group_id_for_claim],
            group_for_claim,
            main_root=main_root,
        )
        if repair_errors:
            _terminate_report_only_repair_after_formal_drift(
                state,
                proving_for_claim,
                group_id_for_claim,
                repair_errors[0],
            )
            _append_event(
                run_root,
                state,
                "group-report-repair-formal-drift",
                round=str(proving_for_claim["round"]),
                group_id=group_id_for_claim,
                boundary="claim",
                first_error=repair_errors[0],
            )
            _save_state(run_root, state)
            print(
                json.dumps(
                    {
                        "status": "invalid-report",
                        "attempt": str(action.get("attempt_id") or ""),
                        "error": repair_errors[0],
                    },
                    indent=2,
                )
            )
            return 1
        expected_report = fixed_path_under(
            Path(str(group_for_claim["report_directory"])),
            Path(str(state["report_root"])),
            label="group report directory",
        )
        expected_input = fixed_path_under(
            expected_report / "group_worker_input.md",
            expected_report,
            label="group worker input",
        )
        expected_terminal_report = fixed_path_under(
            expected_report / "group_worker_report.json",
            expected_report,
            label="group worker terminal report",
        )
        if (
            fixed_path_under(
                Path(str(action.get("input") or "")),
                expected_report,
                label="claimed group worker input",
            )
            != expected_input
            or fixed_path_under(
                Path(str(action.get("report") or "")),
                expected_report,
                label="claimed group worker report",
            )
            != expected_terminal_report
        ):
            raise SystemExit("group delivery paths differ from the pinned manifest")
        if (
            _refresh_group_worker_input(
                state,
                proving_for_claim,
                group_id_for_claim,
                group_for_claim,
            )
            != expected_input
        ):
            raise SystemExit(
                "refreshed group worker input differs from the pinned manifest"
            )
    message = _delivery_message(action)
    attempt_id = str(action.get("attempt_id") or "")
    attempt = _find_round_attempt(state, attempt_id)
    if attempt is not None:
        if attempt.get("status") in {"stale", "superseded", "accepted"}:
            raise SystemExit(
                f"attempt is not startable from status {attempt.get('status')}"
            )
        if attempt.get("status") != "prepared":
            raise SystemExit(
                f"attempt is not prepared for delivery: {attempt.get('status')}"
            )
        annotation = attempt.get("phase") == "annotation"
        if annotation:
            try:
                annotation_paths = _validated_annotation_attempt_paths(
                    state, attempt
                )
            except (OSError, ValueError) as exc:
                raise SystemExit(str(exc)) from exc
            input_path = annotation_paths["input"]
            if not input_path.is_file() or _file_digest(input_path) != attempt.get(
                "input_sha256"
            ):
                raise SystemExit(
                    "annotation agent_input.md changed after controller validation"
                )
            feedback_errors = _feedback_source_reference_errors(state, attempt)
            if feedback_errors:
                raise SystemExit(
                    "annotation feedback source changed before claim: "
                    + feedback_errors[0]
                )
        _bind_delivery_owner(state, attempt, owner, annotation=annotation)
        attempt["status"] = "running"
        claimed_at = _utc()
        attempt["started_at"] = claimed_at
        attempt["delivery"] = {
            "action_id": args.next_action,
            "kind": action["kind"],
            "owner": owner,
            "claimed_at": claimed_at,
        }
        if annotation and isinstance(state.get("annotation_session"), dict):
            state["annotation_session"]["status"] = "running"
    else:
        found = _find_group_attempt(state, attempt_id)
        if found is None:
            raise SystemExit(f"attempt not found: {attempt_id}")
        proving, group_id = found
        if proving.get("status") != "groups-ready":
            raise SystemExit(
                "group attempt does not belong to the current groups-ready vc-proving round"
            )
        group_status = proving["groups"][group_id].get("status")
        if group_status not in {"prepared", "repair-prepared"}:
            raise SystemExit(
                f"group attempt is not prepared for delivery: {group_status}"
            )
        group_state = proving["groups"][group_id]
        _bind_delivery_owner(state, group_state, owner)
        group_state["status"] = "running"
        started_at = _utc()
        group_state["started_at"] = started_at
        group_state["delivery"] = {
            "action_id": args.next_action,
            "kind": action["kind"],
            "owner": owner,
            "claimed_at": started_at,
        }
        intervals = proving.setdefault("timing", {}).setdefault("group-work", [])
        _record_timing_interval(proving, "group-work", started_at=started_at)
        group_state["timing_interval_index"] = len(intervals) - 1
    state["next_actions"] = [
        item for item in state["next_actions"] if item.get("id") != args.next_action
    ]
    state["waiting_for"] = _running_deliveries(state)
    _append_event(
        run_root,
        state,
        "attempt-claimed",
        attempt=attempt_id,
        action=args.next_action,
        owner=owner,
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "claimed",
                "attempt": attempt_id,
                "owner": owner,
                "message": message,
                "handoff": handoff_payload(
                    state, action, message, owner=owner
                ),
                "finalize_invocation": finalize_invocation(
                    state, attempt_id, owner
                ),
            },
            indent=2,
        )
    )
    return 0


def _finalize_delivery_locked(
    args: argparse.Namespace,
    *,
    auto_group_validation: bool = False,
) -> int:
    """Atomically seal returned artifacts and continue controller validation."""

    owner = str(args.owner).strip()
    if not owner:
        raise SystemExit("--owner must be a non-empty stable agent owner")
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _find_round_attempt(state, args.attempt)
    if attempt is not None:
        if attempt.get("phase") == "annotation":
            try:
                annotation_paths = _validated_annotation_attempt_paths(
                    state, attempt
                )
            except (OSError, ValueError) as exc:
                raise SystemExit(str(exc)) from exc
        else:
            annotation_paths = None
        paths = {
            "report": (
                annotation_paths["report"]
                if annotation_paths is not None
                else Path(str(attempt["report"]))
            ),
        }
        delivery = attempt.get("delivery")
        if not isinstance(delivery, dict) or delivery.get("owner") != owner:
            raise SystemExit("attempt was not claimed by this owner")
        current_digests = _artifact_digests(
            paths, main_root=Path(str(state["main_root"]))
        )
        if attempt.get("returned_at") and attempt.get("status") != "running":
            if attempt.get("artifact_sha256") != current_digests:
                raise SystemExit("finalized attempt artifacts changed after return")
            if attempt.get("status") == "returned":
                return _validate_phase_attempt(args)
            print(
                json.dumps(
                    {
                        "status": "already-finalized",
                        "attempt": args.attempt,
                        "owner": owner,
                    },
                    indent=2,
                )
            )
            return 0
        if attempt.get("status") != "running" or not attempt.get("started_at"):
            raise SystemExit("attempt must be claimed before delivery can be finalized")
        if attempt["phase"] == "annotation":
            expected_changed = _annotation_current_changed_files(state, attempt)
            try:
                raw_report = _json_load(paths["report"], {})
            except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
                raw_report = {}
                preflight_errors = [f"annotation report cannot be parsed: {exc}"]
            else:
                preflight_errors = _annotation_report_contract_errors(
                    raw_report if isinstance(raw_report, dict) else {},
                    expected_changed_files=expected_changed,
                    allowed_write_paths=[
                        str(item) for item in attempt.get("allowed_write_paths", [])
                    ],
                )
            if preflight_errors:
                checked_at = _utc()
                attempt["report_preflight"] = {
                    "status": "repair-required",
                    "checked_at": checked_at,
                    "error_count": len(preflight_errors),
                    "first_error": preflight_errors[0],
                }
                _append_event(
                    run_root,
                    state,
                    "annotation-report-preflight-failed",
                    attempt=attempt["attempt_id"],
                    error_count=len(preflight_errors),
                    first_error=preflight_errors[0],
                )
                _save_state(run_root, state)
                print(
                    json.dumps(
                        {
                            "status": "report-repair-required",
                            "attempt": attempt["attempt_id"],
                            "owner": owner,
                            "report": str(paths["report"]),
                            "errors": preflight_errors,
                            "message": (
                                "Continue the same claimed annotation delivery and correct only the terminal report or an out-of-bound formal edit named by this preflight. "
                                "Do not create a new annotation attempt or replace the owner. After the same agent returns, rerun the unchanged finalize-delivery command."
                            ),
                        },
                        indent=2,
                    )
                )
                return 2
            attempt.pop("report_preflight", None)
        elif (
            attempt["phase"] == "vc-checking"
            and attempt.get("proof_reuse_round")
        ):
            # Keep this candidate-repair gate scoped to the sealed-reuse
            # cross-artifact contract. The helper itself gives source drift
            # precedence so the existing mechanical stale transition remains
            # authoritative.
            try:
                raw_report = _json_load(paths["report"], {})
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                raw_report = {}
            preflight_errors: list[str] = []
            if (
                isinstance(raw_report, dict)
                and raw_report.get("status") == "completed"
                and not _minimal_owner_report_errors(
                    raw_report,
                    context="vc-checking",
                    terminal_statuses=PHASE_TERMINAL_STATUSES,
                )
            ):
                # Imported lazily because controller_round_checks imports this
                # lifecycle module. At finalize runtime both modules are
                # initialized by controller_cli, preserving the existing
                # dependency direction without a module cycle.
                from controller_round_checks import (
                    _vc_checking_candidate_preflight_errors,
                )

                preflight_errors.extend(
                    _vc_checking_candidate_preflight_errors(state, attempt)
                )
            if preflight_errors:
                checked_at = _utc()
                attempt["candidate_preflight"] = {
                    "status": "repair-required",
                    "checked_at": checked_at,
                    "error_count": len(preflight_errors),
                    "first_error": preflight_errors[0],
                }
                _append_event(
                    run_root,
                    state,
                    "vc-checking-candidate-preflight-failed",
                    attempt=attempt["attempt_id"],
                    error_count=len(preflight_errors),
                    first_error=preflight_errors[0],
                )
                _save_state(run_root, state)
                report_directory = Path(str(attempt["report_directory"]))
                print(
                    json.dumps(
                        {
                            "status": "report-repair-required",
                            "attempt": attempt["attempt_id"],
                            "owner": owner,
                            "errors": preflight_errors,
                            "repair_boundary": {
                                "group_plan": str(
                                    report_directory / "group_plan.json"
                                ),
                                "reuse_hints": str(
                                    report_directory / "reuse_hints"
                                ),
                                "agent_output": str(attempt["output"]),
                                "agent_report": str(paths["report"]),
                                "formal_source": "read-only",
                            },
                            "message": (
                                "Continue the same claimed vc-checking delivery "
                                "with the same owner. Repair only the reported "
                                "candidate plan/hint contract, update agent_output.md "
                                "only when its explanation changed, and write "
                                "agent_report.json last. Do not create a new round "
                                "or redo unaffected formal analysis. Then rerun this "
                                "unchanged finalize-delivery command."
                            ),
                        },
                        indent=2,
                    )
                )
                return 2
            attempt.pop("candidate_preflight", None)
        attempt["status"] = "returned"
        returned_at = _utc()
        attempt["returned_at"] = returned_at
        attempt["artifact_sha256"] = current_digests
        delivery["finalized_at"] = returned_at
        if attempt["phase"] == "annotation":
            attempt["after_snapshot"] = _archive_annotation_stage(
                state, attempt, "after"
            )
            attempt["changed_files"] = _annotation_changed_files(state, attempt)
            if isinstance(state.get("annotation_session"), dict):
                state["annotation_session"]["status"] = "returned"
        # Report field/diff validation is part of finalization. The next public
        # action is the real controller validation, not a second command whose
        # only purpose is to move `returned` to `ready-for-main-check`.
        state["next_actions"] = []
        state["waiting_for"] = []
    else:
        found = _find_group_attempt(state, args.attempt)
        if found is None:
            raise SystemExit(f"attempt not found: {args.attempt}")
        proving, group_id = found
        if proving.get("status") != "groups-ready":
            raise SystemExit(
                "group attempt does not belong to the current groups-ready vc-proving round"
            )
        integrity_errors = _proving_manifest_errors(state, proving)
        if integrity_errors:
            raise SystemExit(
                "group delivery manifest failed integrity before finalize: "
                + integrity_errors[0]
            )
        group_state = proving["groups"][group_id]
        delivery = group_state.get("delivery")
        if not isinstance(delivery, dict) or delivery.get("owner") != owner:
            raise SystemExit("group attempt was not claimed by this owner")
        manifest = _resolved_proving_manifest(state, proving)
        group = next(
            (
                item
                for item in manifest.get("groups", [])
                if str(item.get("id")) == group_id
            ),
            None,
        )
        if not isinstance(group, dict):
            raise SystemExit(
                f"returned group is missing from the current manifest: {group_id}"
            )
        report_directory = Path(str(group["report_directory"]))
        paths = {
            "report": report_directory / "group_worker_report.json",
            **_group_formal_artifact_paths(group),
        }
        existing_seal = group_state.get("artifact_sha256")
        if isinstance(existing_seal, dict) and "output" in existing_seal:
            paths["output"] = report_directory / "group_worker_output.md"
        repair_errors = _repair_formal_integrity_errors(
            group_state,
            group,
            main_root=main_root,
        )
        if repair_errors:
            _terminate_report_only_repair_after_formal_drift(
                state,
                proving,
                group_id,
                repair_errors[0],
            )
            _append_event(
                run_root,
                state,
                "group-report-repair-formal-drift",
                round=str(proving["round"]),
                group_id=group_id,
                boundary="finalize",
                first_error=repair_errors[0],
            )
            _save_state(run_root, state)
            print(
                json.dumps(
                    {
                        "status": "invalid-report",
                        "attempt": args.attempt,
                        "error": repair_errors[0],
                    },
                    indent=2,
                )
            )
            return 1
        current_digests = _artifact_digests(
            paths, main_root=Path(str(state["main_root"]))
        )
        if group_state.get("returned_at") and group_state.get("status") != "running":
            if group_state.get("artifact_sha256") != current_digests:
                raise SystemExit("finalized group artifacts changed after return")
            print(
                json.dumps(
                    {
                        "status": "already-finalized",
                        "attempt": args.attempt,
                        "owner": owner,
                    },
                    indent=2,
                )
            )
            return 0
        if group_state.get("status") != "running" or not group_state.get("started_at"):
            raise SystemExit(
                "group attempt must be claimed before delivery can be finalized"
            )
        try:
            raw_report = _json_load(paths["report"], {})
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raw_report = {}
            preflight_errors = [f"group report cannot be parsed: {exc}"]
        else:
            preflight_errors = _group_report_contract_errors(
                raw_report if isinstance(raw_report, dict) else {},
                state=state,
                group_state=group_state,
                formal_digests={
                    key: current_digests[key]
                    for key in ("proof_manual", "group_worker_lib")
                    if key in current_digests
                },
                # Version drift is a controller stale outcome handled by the
                # post-seal validation, never an owner report-repair request.
                version_errors=[],
            )
        annotation_gap = (
            isinstance(raw_report, dict)
            and raw_report.get("status") == "blocked"
            and isinstance(raw_report.get("blocker"), dict)
            and raw_report["blocker"].get("failure_class")
            == ANNOTATION_GAP_FAILURE_CLASS
        )
        if annotation_gap:
            output_path = report_directory / "group_worker_output.md"
            try:
                output_digest = _artifact_digests(
                    {"output": output_path},
                    main_root=Path(str(state["main_root"])),
                )["output"]
                output_text = output_path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError, SystemExit) as exc:
                preflight_errors.append(
                    "annotation-gap group requires a readable non-link "
                    f"group_worker_output.md: {exc}"
                )
            else:
                if not output_text.strip():
                    preflight_errors.append(
                        "annotation-gap group requires non-empty "
                        "group_worker_output.md"
                    )
                else:
                    paths["output"] = output_path
                    current_digests["output"] = output_digest
        if preflight_errors:
            checked_at = _utc()
            group_state["repair_formal_sha256"] = {
                key: str(current_digests[key])
                for key in ("proof_manual", "group_worker_lib")
                if current_digests.get(key)
            }
            group_state["report_preflight"] = {
                "status": "repair-required",
                "checked_at": checked_at,
                "error_count": len(preflight_errors),
                "first_error": preflight_errors[0],
            }
            _append_event(
                run_root,
                state,
                "group-report-preflight-failed",
                round=str(proving["round"]),
                group_id=group_id,
                error_count=len(preflight_errors),
                first_error=preflight_errors[0],
            )
            _save_state(run_root, state)
            print(
                json.dumps(
                    {
                        "status": "report-repair-required",
                        "attempt": args.attempt,
                        "owner": owner,
                        "report": str(paths["report"]),
                        "errors": preflight_errors,
                        "message": (
                            "Continue the same claimed group delivery and correct the "
                            "minimal terminal report or the reported formal drift. Then "
                            "rerun this unchanged finalize-delivery command. A worker "
                            "exact check is optional development feedback; controller "
                            "validation after finalize is the acceptance authority."
                        ),
                    },
                    indent=2,
                )
            )
            return 2
        group_state.pop("report_preflight", None)
        group_state.pop("repair_formal_sha256", None)
        group_state["status"] = "returned"
        returned_at = _utc()
        group_state["returned_at"] = returned_at
        delivery["finalized_at"] = returned_at
        interval_index = int(group_state.get("timing_interval_index", -1))
        intervals = proving.setdefault("timing", {}).setdefault("group-work", [])
        if (
            interval_index < 0
            or interval_index >= len(intervals)
            or intervals[interval_index].get("finished_at")
        ):
            raise SystemExit(
                "group attempt timing interval is missing or already closed"
            )
        intervals[interval_index]["finished_at"] = returned_at
        intervals[interval_index]["elapsed_seconds"] = _elapsed_between(
            str(intervals[interval_index]["started_at"]),
            returned_at,
        )
        group_state["artifact_sha256"] = current_digests
        _sync_group_actions(state, proving)
    _append_event(
        run_root,
        state,
        "delivery-finalized",
        attempt=args.attempt,
        owner=owner,
    )
    _save_state(run_root, state)
    if attempt is not None:
        return _validate_phase_attempt(args)
    if auto_group_validation:
        return 0
    print(
        json.dumps(
            {
                "status": "returned",
                "attempt": args.attempt,
                "owner": owner,
                "next_actions": hydrate_actions(
                    state, state.get("next_actions", [])
                ),
            },
            indent=2,
        )
    )
    return 0


def finalize_delivery(args: argparse.Namespace) -> int:
    """Seal one delivery and immediately run its controller validation."""

    if ":" not in str(args.attempt):
        return _finalize_delivery_locked(args)
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    with _state_transaction(run_root):
        returncode = _finalize_delivery_locked(args, auto_group_validation=True)
    if returncode != 0:
        return returncode
    state = _load_state(run_root)
    found = _find_group_attempt(state, args.attempt)
    if found is None:
        raise SystemExit(f"attempt not found after finalize: {args.attempt}")
    proving, group_id = found
    status = str(proving.get("groups", {}).get(group_id, {}).get("status") or "")
    if status == "returned":
        return _validate_group_attempt(run_root, args.attempt)
    return 0


def _group_tooling(
    state: dict[str, Any], proving: dict[str, Any], group: dict[str, Any]
) -> dict[str, Any]:
    run_root = Path(str(state["run_root"]))
    target = state["target_files"]
    directory = Path(str(group["directory"]))
    case_name = str(target["case_name"])
    case_theory = str(target["active_case_theory"])
    build = fixed_path_under(
        group_build_workspace(run_root, str(proving["round"]), directory.name),
        run_root,
        label="group exact-check build workspace",
    )
    coq_group_name = coq_identifier_slug(directory.name)
    debug_script = Path(".coq_debug") / group_debug_script_name(directory.name)
    fixed_path_under(
        build / debug_script,
        build,
        label="canonical group debug script",
    )
    overlays = {
        Path(target["proof_manual_file"]): Path(str(group["proof_manual"])),
    }
    if group.get("group_worker_lib"):
        overlays[Path(target["formal_case_lib"])] = Path(
            str(group["group_worker_lib"])
        )
    return {
        "target_file": Path(".coq_group_checks")
        / f"{case_name}_{coq_group_name}_check.v",
        "build_workspace": build,
        "development_build_workspace": build.parent / "dev",
        "group_check": {
            "case_theory": case_theory,
            "require_modules": [
                case_name + "_goal",
                case_name + "_proof_auto",
                case_name + "_proof_manual",
            ],
            "assigned_witnesses": group_check_names(group),
        },
        "overlays": overlays,
        "debug_script": debug_script,
    }


def _execute_group_check(
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    *,
    development: bool = False,
) -> dict[str, Any]:
    """Shared worker/controller check path; only terminal mode supports acceptance."""

    source_goal_version = str(state.get("source_goal_version", {}).get("digest") or "")
    validation = _group_structure_validation(
        state,
        proving,
        group_id,
        require_complete=not development,
    )
    errors = [str(item) for item in validation["errors"]]
    target_kind = "group-development" if development else "group-check"
    if errors:
        return {
            "status": "failed",
            "returncode": 2,
            "target_kind": target_kind,
            "source_goal_version": source_goal_version,
            "first_failure": validation["first_failure"],
            "stderr_tail": errors[0],
            "elapsed_seconds": 0.0,
            "validation": validation,
        }
    group = validation.get("group")
    if not isinstance(group, dict):
        raise SystemExit("validated group is missing from current manifest")
    tooling = _group_tooling(state, proving, group)
    evidence = run_coqc_check(
        workspace_root=Path(str(state["main_root"])),
        build_workspace=(
            tooling["development_build_workspace"]
            if development
            else tooling["build_workspace"]
        ),
        target_file=(
            Path(str(state["target_files"]["proof_manual_file"]))
            if development
            else tooling["target_file"]
        ),
        target_kind=target_kind,
        source_goal_version=source_goal_version,
        group_check=None if development else tooling["group_check"],
        overlays=tooling["overlays"],
        incremental=development,
        current_case_anchor=Path(str(state["target_files"]["proof_auto_file"])),
    )
    evidence["validation"] = validation
    return evidence


def _validate_group(
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    *,
    run_exact: bool = True,
    exact_evidence: dict[str, Any] | None = None,
) -> tuple[str, list[str], dict[str, Any] | None, bool]:
    """Validate a returned group and, when requested, evaluate exact evidence.

    ``run_exact=False`` performs the sealed report/manifest/version preflight
    only. Group validation uses that mode at its state boundary, runs the
    expensive Rocq check, then calls this function
    again against freshly loaded state with ``exact_evidence``.  Consequently
    unrelated sibling progress is preserved without accepting evidence whose
    source artifacts changed during the check interval.
    """
    integrity_errors = _proving_manifest_errors(state, proving)
    if integrity_errors:
        return "invalid", integrity_errors, None, False
    manifest = _resolved_proving_manifest(state, proving)
    group = next(
        (
            item
            for item in manifest.get("groups", [])
            if str(item.get("id")) == group_id
        ),
        None,
    )
    if not isinstance(group, dict):
        return "invalid", ["group missing from current manifest"], None, False
    report_directory = Path(str(group["report_directory"]))
    group_state = proving.get("groups", {}).get(group_id, {})
    sealed_artifacts = (
        group_state.get("artifact_sha256")
        if isinstance(group_state, dict)
        else {}
    )
    returned_paths = {
        "report": report_directory / "group_worker_report.json",
        **_group_formal_artifact_paths(group),
    }
    if isinstance(sealed_artifacts, dict) and "output" in sealed_artifacts:
        returned_paths["output"] = report_directory / "group_worker_output.md"
    group_artifact_errors = _artifact_integrity_errors(
        returned_paths,
        sealed_artifacts,
        main_root=Path(str(state["main_root"])),
    )
    if group_artifact_errors:
        if exact_evidence is not None:
            return (
                "invalid",
                [
                    "group artifact changed during controller validation: "
                    + str(group_artifact_errors[0])
                ],
                exact_evidence,
                False,
            )
        return "invalid", group_artifact_errors, None, False
    version_errors = _current_version_errors(state)
    if version_errors:
        # The immutable group bytes are intact, so current-source drift is a
        # controller fact and takes precedence over any owner report problem.
        # Do not require even parseable report JSON to route back to annotation.
        return (
            "stale",
            [],
            {"version_drift_errors": version_errors},
            False,
        )
    try:
        report = _json_load(report_directory / "group_worker_report.json", {})
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        message = f"group report cannot be parsed: {exc}"
        return "invalid", [message], None, True
    status = str(report.get("status") or "pending")
    errors = _group_report_contract_errors(
        report if isinstance(report, dict) else {},
        state=state,
        group_state=group_state if isinstance(group_state, dict) else {},
        formal_digests={
            key: str(sealed_artifacts.get(key) or "")
            for key in _group_formal_artifact_paths(group)
            if isinstance(sealed_artifacts, dict)
        },
        version_errors=version_errors,
    )
    effective_status = status
    evidence: dict[str, Any] | None = None
    # Report fields belong to the persistent group owner. If the sealed formal
    # artifacts and current version are intact, malformed terminal metadata is
    # repaired in the same fixed group instead of discarding the proving round.
    repairable_group_failure = bool(errors)
    annotation_gap_report = (
        effective_status == "blocked"
        and isinstance(report, dict)
        and isinstance(report.get("blocker"), dict)
        and report["blocker"].get("failure_class")
        == ANNOTATION_GAP_FAILURE_CLASS
    )
    if annotation_gap_report and (
        not isinstance(sealed_artifacts, dict) or "output" not in sealed_artifacts
    ):
        errors.append("annotation-gap group Markdown was not sealed at finalize")
        repairable_group_failure = False
    if (
        annotation_gap_report
        and not errors
    ):
        location = str(report["blocker"].get("location") or "")
        assigned_witnesses = [
            str(witness.get("name") or "")
            for witness in group.get("witnesses", [])
            if isinstance(witness, dict) and witness.get("name")
        ]
        if not any(
            re.search(
                rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])",
                location,
            )
            for name in assigned_witnesses
        ):
            errors.append(
                "annotation-gap blocker.location must name an assigned witness"
            )
            repairable_group_failure = True
        # An annotation gap may leave assigned proofs unfinished, so it does
        # not run the exact group Rocq target.  It must still preserve every
        # protected token, helper/import boundary, and safety rule before its
        # sealed bytes can become a conditional reuse source.
        if not errors:
            validation = _group_structure_validation(
                state,
                proving,
                group_id,
                require_complete=False,
            )
            structure_errors = [
                str(item) for item in validation.get("errors", [])
            ]
            if structure_errors:
                errors.extend(structure_errors)
                repairable_group_failure = bool(validation.get("recoverable"))
                evidence = {
                    "first_failure": validation.get("first_failure"),
                }
    if effective_status == "completed":
        if not errors:
            if not run_exact:
                return effective_status, errors, None, False
            evidence = (
                exact_evidence
                if exact_evidence is not None
                else _execute_group_check(state, proving, group_id)
            )
            validation = (
                _group_structure_validation(
                    state,
                    proving,
                    group_id,
                    require_complete=True,
                )
                if exact_evidence is not None
                else evidence.get("validation", {})
            )
            structure_errors = [
                str(item)
                for item in (
                    validation.get("errors", []) if isinstance(validation, dict) else []
                )
            ]
            errors.extend(structure_errors)
            repairable_group_failure = bool(
                structure_errors
                and isinstance(validation, dict)
                and validation.get("recoverable")
            )
            if not structure_errors and evidence.get("status") != "passed":
                first_failure = evidence.get("first_failure")
                failure = first_failure if isinstance(first_failure, dict) else {}
                category = str(failure.get("category") or "")
                message = str(
                    failure.get("message")
                    or evidence.get("stderr_tail")
                    or "controller exact group-check failed"
                )
                errors.append(message)
                repairable_group_failure = category in {"rocq", "tool"}
            validation_drift = _artifact_integrity_errors(
                {
                    "report": report_directory / "group_worker_report.json",
                    **_group_formal_artifact_paths(group),
                },
                proving.get("groups", {}).get(group_id, {}).get("artifact_sha256"),
                main_root=Path(str(state["main_root"])),
            )
            if validation_drift:
                errors.append(
                    "group artifact changed during controller validation: "
                    + str(validation_drift[0])
                )
                # The exact check no longer describes the sealed bytes.  This
                # is provenance drift, not an owner-editable proof failure;
                # never reopen the group and silently reseal changed formals.
                repairable_group_failure = False
    return effective_status, errors, evidence, repairable_group_failure


def _promote_group_public_helpers(
    state: dict[str, Any], proving: dict[str, Any], group: dict[str, Any]
) -> dict[str, Any]:
    """Append controller-planned, group-checked helpers to the run-local pool."""

    pool_errors = _public_helper_pool_errors(state)
    if pool_errors:
        raise ValueError(pool_errors[0])
    planned_names = {
        str(item.get("name") or "")
        for item in group.get("helpers", [])
        if isinstance(item, dict)
        and item.get("name")
        and (
            item.get("visibility") == "public"
        )
    }
    if not group.get("group_worker_lib"):
        if group.get("helpers"):
            raise ValueError("planned helpers require a group_worker_lib candidate")
        return {
            "status": "unchanged",
            "appended_count": 0,
            "skipped_count": 0,
            "conflict_count": 0,
        }
    if not planned_names:
        return {
            "status": "unchanged",
            "appended_count": 0,
            "skipped_count": 0,
            "conflict_count": 0,
        }
    main_root = Path(str(state["main_root"]))
    seed_path = main_root / str(state["target_files"]["formal_case_lib"])
    group_path = Path(str(group["group_worker_lib"]))
    expected_group_sha256 = str(
        proving.get("groups", {})
        .get(str(group["id"]), {})
        .get("artifact_sha256", {})
        .get("group_worker_lib")
        or ""
    )
    group_bytes = group_path.read_bytes()
    if (
        not expected_group_sha256
        or sha256_bytes(group_bytes) != expected_group_sha256
    ):
        raise ValueError("group_worker_lib changed before public-helper promotion")
    seed_declarations = parse_lib_declarations(seed_path.read_text(encoding="utf-8"))
    seed_keys = {(str(item["kind"]), str(item["name"])) for item in seed_declarations}
    additions = [
        item
        for item in parse_lib_declarations(group_bytes.decode("utf-8"))
        if (str(item["kind"]), str(item["name"])) not in seed_keys
    ]
    helper_additions = {
        str(item["name"]): item
        for item in additions
        if str(item["kind"]) in HELPER_DECL_KINDS and item.get("name")
    }
    selected_names = set(planned_names) & set(helper_additions)
    pending = list(selected_names)
    while pending:
        selected_name = pending.pop()
        block = str(helper_additions[selected_name].get("block") or "")
        referenced_names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", block)) & set(
            helper_additions
        )
        for dependency in sorted(referenced_names - selected_names):
            selected_names.add(dependency)
            pending.append(dependency)
    selected_helpers = [
        item for item in additions if str(item.get("name") or "") in selected_names
    ]
    if not selected_helpers:
        return {
            "status": "unchanged",
            "appended_count": 0,
            "skipped_count": 0,
            "conflict_count": 0,
        }
    selected = [
        item for item in additions if str(item["kind"]) == "Import"
    ] + selected_helpers
    run_root = Path(str(state["run_root"]))
    pool_path = public_helper_lemma_lib_path(run_root)
    pending_transaction = state.get("public_helper_promotion_transaction")
    if isinstance(pending_transaction, dict):
        if str(pending_transaction.get("round") or "") != str(proving["round"]) or str(
            pending_transaction.get("group_id") or ""
        ) != str(group["id"]):
            raise ValueError(
                "another public-helper promotion transaction must be recovered first"
            )
        current = public_helper_pool_snapshot(pool_path)
        if current["sha256"] == pending_transaction.get("after_sha256"):
            _refresh_public_helper_pool_state(state)
            pending_transaction["status"] = "applied"
            return dict(pending_transaction["summary"])
        if current["sha256"] != pending_transaction.get("before_sha256"):
            raise ValueError(
                "pending public-helper promotion no longer matches the live pool"
            )

    plan = plan_public_helper_declarations(
        pool_path,
        selected,
        source_round=str(proving["round"]),
        source_group=str(group["id"]),
    )
    summary = {
        "status": str(plan["status"]),
        "appended_count": len(plan["appended"]),
        "skipped_count": len(plan["skipped"]),
        "conflict_count": len(plan["conflicts"]),
        **({"first_conflict": str(plan["conflicts"][0])} if plan["conflicts"] else {}),
    }
    if plan["after_sha256"] == plan["before_sha256"]:
        return summary

    if isinstance(pending_transaction, dict):
        if (
            pending_transaction.get("before_sha256") != plan["before_sha256"]
            or pending_transaction.get("after_sha256") != plan["after_sha256"]
            or pending_transaction.get("summary") != summary
        ):
            raise ValueError(
                "recomputed public-helper candidate does not match its pending receipt"
            )
    else:
        pending_transaction = {
            "status": "prepared",
            "round": str(proving["round"]),
            "group_id": str(group["id"]),
            "before_sha256": str(plan["before_sha256"]),
            "after_sha256": str(plan["after_sha256"]),
            "summary": summary,
            "prepared_at": _utc(),
        }
        state["public_helper_promotion_transaction"] = pending_transaction
        _append_event(
            run_root,
            state,
            "public-helper-promotion-prepared",
            round=str(proving["round"]),
            group_id=str(group["id"]),
            before_sha256=str(plan["before_sha256"]),
            after_sha256=str(plan["after_sha256"]),
        )
        # Persist the exact recovery receipt before replacing the live pool.
        _save_state(run_root, state)

    apply_public_helper_declaration_plan(pool_path, plan)
    _refresh_public_helper_pool_state(state)
    pending_transaction["status"] = "applied"
    _append_event(
        run_root,
        state,
        "public-helper-pool-updated",
        round=str(proving["round"]),
        group_id=str(group["id"]),
        appended_count=summary["appended_count"],
        conflict_count=summary["conflict_count"],
    )
    return summary


def _prepare_group_repair(
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    failure: str,
    failure_details: dict[str, Any] | None = None,
    preserve_formal: bool = False,
) -> None:
    """Return a recoverable validation failure to the same fixed worker."""

    manifest = _resolved_proving_manifest(state, proving)
    group = next(
        item
        for item in manifest["groups"]
        if isinstance(item, dict) and str(item.get("id")) == group_id
    )
    group_state = proving["groups"][group_id]
    repair_index = int(group_state.get("repair_index", 0)) + 1
    group_state["repair_index"] = repair_index
    feedback = (
        {
            "category": str(failure_details.get("category") or "group-check"),
            "kind": str(failure_details.get("kind") or "group-check"),
            "message": str(failure_details.get("message") or failure),
            "repair": str(
                failure_details.get("repair")
                or "Rerun the exact controller check and repair only owner-editable proof/helper content."
            ),
            "recoverable": True,
        }
        if isinstance(failure_details, dict)
        else _group_failure_details(failure, recoverable=True)
    )
    group_state["repair_feedback"] = feedback
    group_state["validation_errors"] = [failure]
    group_state["status"] = "repair-prepared"
    sealed_artifacts = group_state.get("artifact_sha256")
    if preserve_formal and isinstance(sealed_artifacts, dict):
        group_state["repair_formal_sha256"] = {
            key: str(sealed_artifacts[key])
            for key in ("proof_manual", "group_worker_lib")
            if sealed_artifacts.get(key)
        }
    else:
        group_state.pop("repair_formal_sha256", None)
    group_state.pop("report_preflight", None)
    group_state.pop("artifact_sha256", None)
    group_state.pop("accepted_artifact_sha256", None)
    group_state.pop("accepted_at", None)
    _refresh_group_worker_input(state, proving, group_id, group)


def _returned_group_for_validation(
    state: dict[str, Any], attempt_id: str
) -> tuple[dict[str, Any], str]:
    """Resolve one finalized group from freshly loaded controller state."""

    found = _find_group_attempt(state, attempt_id)
    if found is None:
        raise SystemExit(f"attempt not found: {attempt_id}")
    proving, group_id = found
    if proving.get("status") != "groups-ready":
        raise SystemExit(
            "group attempt does not belong to the current groups-ready vc-proving round"
        )
    if proving.get("groups", {}).get(group_id, {}).get("status") != "returned":
        raise SystemExit("group attempt must be finalized before validation")
    return proving, group_id


def _apply_group_validation_result(
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    *,
    status: str,
    errors: list[str],
    evidence: dict[str, Any] | None,
    repairable_group_failure: bool,
) -> tuple[str, list[str]]:
    """Apply one already-evaluated group result to the current locked state."""

    if errors and repairable_group_failure:
        errors = [str(errors[0])]
        failure_details = (
            evidence.get("first_failure")
            if isinstance(evidence, dict)
            and isinstance(evidence.get("first_failure"), dict)
            else None
        )
        _prepare_group_repair(
            state,
            proving,
            group_id,
            str(errors[0]),
            failure_details=failure_details,
            preserve_formal=evidence is None,
        )
        result_status = "repair-prepared"
    elif errors:
        errors = [str(errors[0])]
        proving["groups"][group_id]["status"] = "invalid-report"
        proving["groups"][group_id]["validation_errors"] = [str(errors[0])]
        if evidence:
            proving["groups"][group_id]["group_check"] = {
                key: evidence.get(key)
                for key in (
                    "status",
                    "returncode",
                    "source_goal_version",
                    "first_failure",
                )
            }
        result_status = "invalid-report"
    elif status == "completed":
        if not isinstance(evidence, dict) or evidence.get("status") != "passed":
            raise SystemExit(
                "completed group validation is missing passed Coq check evidence"
            )
        group_state = proving["groups"][group_id]
        manifest = _resolved_proving_manifest(state, proving)
        group = next(item for item in manifest["groups"] if str(item["id"]) == group_id)
        report_directory = Path(str(group["report_directory"]))
        try:
            promotion = _promote_group_public_helpers(state, proving, group)
        except (OSError, UnicodeDecodeError, ValueError) as exc:
            raise SystemExit(
                f"controller could not append checked public helper candidates: {exc}"
            ) from exc
        group_state["status"] = "accepted"
        group_state.pop("repair_feedback", None)
        group_state.pop("validation_errors", None)
        group_state.pop("validation_reason", None)
        group_state.pop("stale_reason", None)
        group_state.pop("repair_formal_sha256", None)
        group_state["group_check"] = {
            key: evidence.get(key)
            for key in ("status", "returncode", "source_goal_version")
        }
        group_state["public_helper_promotion"] = {
            "status": str(promotion.get("status") or "unchanged"),
            "appended_count": int(promotion.get("appended_count", 0)),
            "skipped_count": int(promotion.get("skipped_count", 0)),
            "conflict_count": int(promotion.get("conflict_count", 0)),
            **(
                {"first_conflict": str(promotion["first_conflict"])}
                if promotion.get("first_conflict")
                else {}
            ),
        }
        group_state["accepted_artifact_sha256"] = _artifact_digests(
            {
                "report": report_directory / "group_worker_report.json",
                **_group_formal_artifact_paths(group),
            },
            main_root=Path(str(state["main_root"])),
        )
        group_state["accepted_at"] = _utc()
        pending_promotion = state.get("public_helper_promotion_transaction")
        if (
            isinstance(pending_promotion, dict)
            and str(pending_promotion.get("round") or "") == str(proving["round"])
            and str(pending_promotion.get("group_id") or "") == group_id
            and pending_promotion.get("status") == "applied"
        ):
            # Group acceptance and removal of the recovery receipt are one
            # state commit. Before this point, rerunning the same validation can
            # deterministically finish either side of the interrupted append.
            state.pop("public_helper_promotion_transaction", None)
        result_status = "accepted"
    elif status == "compact-error":
        group_state = proving["groups"][group_id]
        attempt_index = int(group_state.get("attempt_index", 1))
        manifest = _resolved_proving_manifest(state, proving)
        group_entry = next(
            item for item in manifest["groups"] if str(item["id"]) == group_id
        )
        group_state.setdefault("compact_attempts", []).append(
            {
                "attempt_index": attempt_index,
                "recorded_at": _utc(),
            }
        )
        if attempt_index < int(state["max_compact_attempts"]):
            group_state["attempt_index"] = attempt_index + 1
            group_state["status"] = "prepared"
            for field in (
                "owner",
                "delivery",
                "started_at",
                "returned_at",
                "artifact_sha256",
                "report_preflight",
            ):
                group_state.pop(field, None)
            _refresh_group_worker_input(
                state,
                proving,
                group_id,
                group_entry,
            )
            result_status = "compact-retry-prepared"
        else:
            group_state["status"] = "compact-error-retry-exhausted"
            group_state["blockers"] = [
                {
                    "failure_class": "compact-error-retry-exhausted",
                    "round": str(proving["round"]),
                    "group_id": group_id,
                    "attempt_index": attempt_index,
                }
            ]
            result_status = "compact-error-retry-exhausted"
    else:
        manifest = _resolved_proving_manifest(state, proving)
        group_entry = next(
            item for item in manifest["groups"] if str(item["id"]) == group_id
        )
        group_state = proving["groups"][group_id]
        group_state["status"] = status
        if status == "stale":
            version_errors = (
                list(evidence.get("version_drift_errors", []))
                if isinstance(evidence, dict)
                and isinstance(evidence.get("version_drift_errors"), list)
                else _current_version_errors(state)
            )
            if not version_errors:
                raise SystemExit(
                    "stale group validation lost its mechanical version-drift evidence"
                )
            receipt = {
                "failure_class": "current-version-drift",
                "action": "group-worker-validation",
                "round": str(proving["round"]),
                "group_id": group_id,
                "message": str(version_errors[0]),
                "error_count": len(version_errors),
                "detected_at": _utc(),
            }
            group_state["stale_reason"] = str(version_errors[0])
            group_state["version_drift"] = receipt
            group_state["blockers"] = [receipt]
            state["current_blockers"] = [receipt]
        else:
            report_path = fixed_path_under(
                Path(str(group_entry["report_directory"])) / "group_worker_report.json",
                Path(str(group_entry["report_directory"])),
                label="group worker terminal report",
            )
            report = _json_load(report_path, {})
            blocker = report.get("blocker")
            group_state["blockers"] = [blocker] if isinstance(blocker, dict) else []
        result_status = status
    return result_status, errors


def _commit_group_validation(
    run_root: Path,
    state: dict[str, Any],
    proving: dict[str, Any],
    group_id: str,
    *,
    status: str,
    errors: list[str],
    evidence: dict[str, Any] | None,
    repairable_group_failure: bool,
) -> tuple[str, list[str]]:
    """Commit a validated result after the caller reloads current run state."""

    result_status, errors = _apply_group_validation_result(
        state,
        proving,
        group_id,
        status=status,
        errors=errors,
        evidence=evidence,
        repairable_group_failure=repairable_group_failure,
    )
    _sync_group_actions(state, proving)
    _append_event(
        run_root,
        state,
        "group-attempt-validated",
        group_id=group_id,
        status=result_status,
        errors=errors,
        **(
            {"first_failure": evidence["first_failure"]}
            if isinstance(evidence, dict) and evidence.get("first_failure")
            else {}
        ),
    )
    _save_state(run_root, state)
    return result_status, errors


def _group_validation_response(
    result_status: str,
    errors: list[str],
    evidence: dict[str, Any] | None,
) -> int:
    response: dict[str, Any] = {"status": result_status, "errors": errors}
    if isinstance(evidence, dict) and evidence.get("first_failure"):
        response["first_failure"] = evidence["first_failure"]
    print(json.dumps(response, indent=2))
    return (
        0
        if result_status
        in {
            "accepted",
            "blocked",
            "stale",
            "compact-retry-prepared",
            "compact-error-retry-exhausted",
            "repair-prepared",
        }
        else 1
    )


def _validate_group_attempt(run_root: Path, attempt_id: str) -> int:
    """Validate one group while preserving fresh state around exact Rocq work."""

    with _state_transaction(run_root):
        state = _load_state(run_root)
        proving, group_id = _returned_group_for_validation(state, attempt_id)
        status, errors, evidence, repairable = _validate_group(
            state,
            proving,
            group_id,
            run_exact=False,
        )
        if status != "completed" or errors:
            result_status, errors = _commit_group_validation(
                run_root,
                state,
                proving,
                group_id,
                status=status,
                errors=errors,
                evidence=evidence,
                repairable_group_failure=repairable,
            )
            return _group_validation_response(result_status, errors, evidence)

        # Keep this immutable Python snapshot only as the exact-check input. It
        # is never written back after the long check; the commit path
        # below reloads state and revalidates every sealed source artifact.
        validation_state = state
        validation_proving = proving

    evidence = _execute_group_check(validation_state, validation_proving, group_id)

    with _state_transaction(run_root):
        state = _load_state(run_root)
        proving, current_group_id = _returned_group_for_validation(state, attempt_id)
        if current_group_id != group_id:
            raise SystemExit("group validation target changed during Coq check")
        status, errors, _ignored, repairable = _validate_group(
            state,
            proving,
            group_id,
            exact_evidence=evidence,
        )
        result_status, errors = _commit_group_validation(
            run_root,
            state,
            proving,
            group_id,
            status=status,
            errors=errors,
            evidence=evidence,
            repairable_group_failure=repairable,
        )
    return _group_validation_response(result_status, errors, evidence)


def _validate_phase_attempt(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _find_round_attempt(state, args.attempt)
    if attempt is None:
        raise SystemExit(f"attempt not found: {args.attempt}")
    if attempt.get("status") != "returned":
        raise SystemExit("attempt must be finalized before validation")
    if attempt.get("phase") == "annotation":
        try:
            annotation_paths = _validated_annotation_attempt_paths(state, attempt)
        except (OSError, ValueError) as exc:
            raise SystemExit(str(exc)) from exc
        report_path = annotation_paths["report"]
    else:
        report_path = _attempt_artifact(state, attempt, "report")
    artifact_errors = _artifact_integrity_errors(
        {"report": report_path},
        attempt.get("artifact_sha256"),
        main_root=Path(str(state["main_root"])),
    )
    parse_errors: list[str] = []
    try:
        report = _json_load(report_path, {})
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        report = {}
        parse_errors.append(f"agent report cannot be parsed: {exc}")
    status = str(report.get("status") or "pending")
    errors: list[str] = [*artifact_errors, *parse_errors]
    version_errors = (
        _current_version_errors(state) if attempt["phase"] == "vc-checking" else []
    )
    annotation_history_errors: list[str] = []
    if attempt["phase"] == "annotation":
        input_path = annotation_paths["input"]
        if not input_path.is_file() or _file_digest(input_path) != attempt.get(
            "input_sha256"
        ):
            errors.append(
                "annotation agent_input.md changed after controller validation"
            )
        annotation_history_errors = _annotation_after_snapshot_errors(state, attempt)
        errors.extend(_annotation_after_drift_errors(state, attempt))
        attempt["changed_files"] = _annotation_changed_files(state, attempt)
        errors.extend(
            _annotation_report_contract_errors(
                report if isinstance(report, dict) else {},
                expected_changed_files=attempt["changed_files"],
                allowed_write_paths=[
                    str(item) for item in attempt.get("allowed_write_paths", [])
                ],
            )
        )
    else:
        errors.extend(
            _minimal_owner_report_errors(
                report if isinstance(report, dict) else {},
                context="vc-checking",
                terminal_statuses=PHASE_TERMINAL_STATUSES,
            )
        )
        if status == "stale" and not version_errors:
            errors.append(
                "stale vc-checking status requires mechanically detected version drift"
            )
    effective_status = "stale" if version_errors else status
    if attempt["phase"] == "vc-checking" and status == "completed":
        if str((state.get("source_version") or {}).get("digest") or "") != attempt.get(
            "source_version"
        ):
            errors.append("vc-checking input source_version is stale")
    if attempt["phase"] == "vc-checking" and version_errors and not artifact_errors:
        # Once the sealed report bytes are known intact, mechanical
        # source drift outranks owner metadata mistakes (including malformed
        # JSON). A same-phase retry would be created against the same stale
        # annotation and repeat forever.
        if errors:
            attempt["secondary_validation_errors"] = [str(item) for item in errors]
        _transition_current_version_drift(
            state,
            attempt,
            action="vc-checking-validation",
            feedback_attempt_id=str(attempt["attempt_id"]),
        )
        attempt["finished_at"] = _utc()
        result_status = "stale"
        errors = []
    elif errors:
        attempt["status"] = "invalid-report"
        attempt["validation_errors"] = errors
        attempt["finished_at"] = _utc()
        result_status = "invalid-report"
        if attempt.get("phase") == "annotation" and isinstance(
            state.get("annotation_session"), dict
        ):
            state["annotation_session"]["status"] = "idle"
        if artifact_errors:
            # A changed sealed report cannot safely become retry input.
            # Stop with an explicit existing invalid-report blocker instead of
            # leaving the finalized delivery without a next action.
            state["next_actions"] = []
            state["current_blockers"] = [
                {
                    "failure_class": "invalid-report",
                    "message": str(artifact_errors[0]),
                }
            ]
        elif annotation_history_errors:
            state["next_actions"] = []
            state["current_blockers"] = [
                {
                    "failure_class": "annotation-history-artifact-drift",
                    "attempt_id": str(attempt["attempt_id"]),
                    "first_error": str(annotation_history_errors[0]),
                    "error_count": len(annotation_history_errors),
                }
            ]
        elif attempt["phase"] == "annotation":
            _queue_annotation_feedback(
                state, attempt["attempt_id"], "annotation-invalid-report"
            )
        else:
            _queue_vc_checking_retry(
                state,
                attempt,
                "vc-checking-invalid-report",
            )
    elif effective_status == "completed":
        attempt["status"] = "ready-for-main-check"
        result_status = "ready-for-main-check"
        if attempt.get("phase") == "annotation" and isinstance(
            state.get("annotation_session"), dict
        ):
            state["annotation_session"]["status"] = "awaiting-main-check"
        state["next_actions"] = [
            {
                "id": f"{attempt['phase']}-check-{attempt['round']}",
                "kind": "main-owned-action",
                "action": "annotation-check-round"
                if attempt["phase"] == "annotation"
                else "vc-checking-check-round",
                "round": attempt["round"],
                "attempt_id": attempt["attempt_id"],
            }
        ]
    else:
        attempt["status"] = effective_status
        attempt["finished_at"] = _utc()
        result_status = effective_status
        if effective_status == "stale" and version_errors:
            attempt["stale_reason"] = version_errors[0]
        if attempt.get("phase") == "annotation" and isinstance(
            state.get("annotation_session"), dict
        ):
            state["annotation_session"]["status"] = "idle"
        if effective_status == "blocked" and attempt["phase"] == "vc-checking":
            blocker = report.get("blocker")
            if not isinstance(blocker, dict):
                raise SystemExit("validated vc-checking blocker is unavailable")
            failure_class = str(blocker["failure_class"])
            retry_phase = VC_CHECKING_BLOCKER_RETRY_PHASES[failure_class]
            retry_reason = f"vc-checking-{failure_class}"
            if retry_phase == "annotation":
                _queue_annotation_feedback(
                    state,
                    attempt["attempt_id"],
                    retry_reason,
                )
            else:
                _queue_vc_checking_retry(
                    state,
                    attempt,
                    retry_reason,
                    blocker=blocker,
                )
        elif effective_status in {"blocked", "stale"}:
            _queue_annotation_feedback(
                state,
                attempt["attempt_id"],
                f"{attempt['phase']}-{effective_status}",
            )
        elif (
            effective_status == "compact-error" and attempt.get("phase") == "annotation"
        ):
            _queue_annotation_feedback(
                state, attempt["attempt_id"], "annotation-compact-error"
            )
        elif effective_status == "compact-error":
            _queue_vc_checking_retry(
                state,
                attempt,
                "vc-checking-compact-error",
                compact=True,
            )
    _append_event(
        run_root,
        state,
        "round-attempt-validated",
        attempt=attempt["attempt_id"],
        status=result_status,
        errors=errors,
    )
    _save_state(run_root, state)
    print(json.dumps({"status": result_status, "errors": errors}, indent=2))
    return (
        0
        if result_status
        in {"ready-for-main-check", "blocked", "stale", "compact-error"}
        else 1
    )


def _attempt_for_round(
    state: dict[str, Any], round_id: str, expected_phase: str
) -> dict[str, Any]:
    round_state = state["rounds"].get(round_id)
    if not isinstance(round_state, dict) or round_state.get("phase") != expected_phase:
        raise SystemExit(f"{expected_phase} round not found: {round_id}")
    attempt = state["attempts"].get(round_state.get("current_attempt"))
    if (
        not isinstance(attempt, dict)
        or attempt.get("round") != round_id
        or attempt.get("phase") != expected_phase
    ):
        raise SystemExit(f"{expected_phase} round attempt identity is invalid")
    try:
        _validated_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        raise SystemExit(
            f"{expected_phase} round attempt path topology is invalid: {exc}"
        ) from exc
    return attempt


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
            previous_status = str(attempt.get("status") or "")
            if attempt.get("phase") == VC_PROVING_PHASE:
                attempt["stale_from_status"] = previous_status
                attempt["proof_reuse_eligible"] = previous_status in {
                    "groups-ready",
                    "parent-verify-failed",
                    "verified",
                }
            attempt["status"] = "stale"
            attempt["stale_reason"] = reason
            attempt.setdefault("finished_at", _utc())
    accepted_keys = {"vc-checking", VC_PROVING_PHASE}
    if phase == "annotation":
        accepted_keys.add("annotation")
    for key in accepted_keys:
        state.get("accepted_rounds", {}).pop(key, None)
    state["final_candidate"] = None
    final_apply = (
        state.get("final_apply") if isinstance(state.get("final_apply"), dict) else {}
    )
    if final_apply.get("status") == "passed":
        raise SystemExit(
            "cannot retry while a final candidate is applied; run final-check so it passes or rolls back first"
        )
    state["final_apply"] = None
    state["final_check"] = None
    state["current_blockers"] = []


def _feedback_source(
    state: dict[str, Any], identifier: str
) -> tuple[dict[str, str], dict[str, Any]]:
    attempt = _find_round_attempt(state, identifier)
    if attempt is not None:
        markdown = _attempt_artifact(state, attempt, "output")
        report = _attempt_artifact(state, attempt, "report")
        source = {
            "phase": str(attempt["phase"]),
            "attempt_id": str(attempt["attempt_id"]),
            "markdown": str(markdown),
            "json": str(report),
        }
        integrity_errors = _artifact_integrity_errors(
            {"report": report},
            attempt.get("artifact_sha256"),
            main_root=Path(str(state["main_root"])),
        )
        if integrity_errors:
            raise SystemExit(
                "annotation feedback artifacts are not immutable: "
                + "; ".join(integrity_errors)
            )
        try:
            payload = _json_load(report, {})
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            # Feedback files are immutable references, not acceptance
            # evidence. A malformed sealed report can still be cited by path;
            # controller-owned blockers carry the actionable cause.
            payload = {}
    else:
        found = _find_group_attempt(state, identifier)
        if found is None:
            raise SystemExit(f"feedback attempt not found: {identifier}")
        proving, group_id = found
        manifest = _resolved_proving_manifest(state, proving)
        group = next(
            (
                item
                for item in manifest.get("groups", [])
                if str(item.get("id")) == group_id
            ),
            None,
        )
        if not isinstance(group, dict):
            raise SystemExit(
                f"feedback group is missing from the current manifest: {identifier}"
            )
        report_directory = fixed_path_under(
            Path(str(group["report_directory"])),
            Path(str(state["report_root"])),
            label="feedback group report directory",
        )
        markdown = fixed_path_under(
            report_directory / "group_worker_output.md",
            report_directory,
            label="feedback group Markdown",
        )
        report = fixed_path_under(
            report_directory / "group_worker_report.json",
            report_directory,
            label="feedback group JSON",
        )
        source = {
            "phase": "group-worker",
            "attempt_id": identifier,
            "markdown": str(markdown),
            "json": str(report),
        }
        expected_artifacts = (
            proving.get("groups", {}).get(group_id, {}).get("artifact_sha256")
        )
        group_state = proving.get("groups", {}).get(group_id, {})
        blockers = (
            group_state.get("blockers") if isinstance(group_state, dict) else None
        )
        annotation_gap_source = (
            isinstance(group_state, dict)
            and group_state.get("status") == "blocked"
            and isinstance(blockers, list)
            and len(blockers) == 1
            and isinstance(blockers[0], dict)
            and blockers[0].get("failure_class")
            == ANNOTATION_GAP_FAILURE_CLASS
        )
        if annotation_gap_source and (
            not isinstance(expected_artifacts, dict)
            or "output" not in expected_artifacts
        ):
            raise SystemExit(
                "annotation-gap feedback lacks a sealed group_worker_output.md"
            )
        feedback_artifacts = {"report": report}
        if isinstance(expected_artifacts, dict) and "output" in expected_artifacts:
            feedback_artifacts["output"] = markdown
        integrity_errors = _artifact_integrity_errors(
            feedback_artifacts,
            expected_artifacts,
            main_root=Path(str(state["main_root"])),
        )
        if integrity_errors:
            raise SystemExit(
                "annotation feedback artifacts are not immutable: "
                + "; ".join(integrity_errors)
            )
        try:
            payload = _json_load(report, {})
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            payload = {}
    missing = [source["json"]] if not Path(source["json"]).is_file() else []
    if missing:
        raise SystemExit(
            "annotation feedback requires its terminal JSON source: "
            + ", ".join(missing)
        )
    return source, payload if isinstance(payload, dict) else {}


def _feedback_source_reference_errors(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    """Revalidate every original feedback path immediately before handoff."""

    errors: list[str] = []
    for expected in attempt.get("feedback_sources", []):
        if not isinstance(expected, dict):
            errors.append("annotation feedback source record is invalid")
            continue
        identifier = str(expected.get("attempt_id") or "")
        try:
            current, _payload = _feedback_source(state, identifier)
        except (OSError, ValueError, SystemExit) as exc:
            errors.append(str(exc))
            continue
        if current != expected:
            errors.append(
                "annotation feedback source topology changed: " + identifier
            )
    return errors


def _feedback_sources_for_retry(
    state: dict[str, Any], identifier: str
) -> tuple[list[dict[str, str]], list[dict[str, Any]], list[dict[str, Any]]]:
    """Resolve one ordinary source or one proving-round gap aggregate.

    ``retry-round`` intentionally keeps one ``--previous-attempt`` argument.
    For an annotation-gap proving round that identifier names the round; this
    function expands it to every original group Markdown/JSON source in
    accepted-plan order and rechecks each sealed JSON blocker.
    """

    proving = state.get("attempts", {}).get(identifier)
    if not isinstance(proving, dict) or proving.get("phase") != VC_PROVING_PHASE:
        source, payload = _feedback_source(state, identifier)
        return [source], [payload], []

    manifest_errors = _proving_manifest_errors(state, proving)
    if manifest_errors:
        raise SystemExit(
            "vc-proving annotation-gap feedback manifest changed: "
            + manifest_errors[0]
        )
    manifest = _resolved_proving_manifest(state, proving)
    groups = [
        group
        for group in manifest.get("groups", [])
        if isinstance(group, dict)
    ]
    if not groups or not _reuse_group_artifacts_are_sealed(proving, groups):
        raise SystemExit(
            "vc-proving annotation-gap feedback lacks an intact full-round reuse seal"
        )
    records = _annotation_gap_feedback_records(proving, manifest)
    if not records:
        raise SystemExit(
            "vc-proving feedback source has no sealed annotation-gap blockers"
        )
    manifest_group_ids = {str(group.get("id") or "") for group in groups}
    accepted_group_ids = {
        str(group_id)
        for group_id, group_state in proving.get("groups", {}).items()
        if isinstance(group_state, dict) and group_state.get("status") == "accepted"
    }
    annotation_gap_group_ids = {
        str(record["group_id"]) for record in records
    }
    if accepted_group_ids | annotation_gap_group_ids != manifest_group_ids:
        raise SystemExit(
            "vc-proving annotation-gap feedback was requested before every "
            "planned group reached a valid terminal state"
        )
    if state.get("current_blockers") != records:
        raise SystemExit(
            "vc-proving annotation-gap feedback differs from the current "
            "controller blocker aggregate"
        )
    sources: list[dict[str, str]] = []
    payloads: list[dict[str, Any]] = []
    blocker_fields = (
        "failure_class",
        "kind",
        "location",
        "message",
        "repair_boundary",
    )
    for record in records:
        group_id = str(record["group_id"])
        source, payload = _feedback_source(
            state, f"{proving['round']}:{group_id}"
        )
        expected_blocker = {field: record[field] for field in blocker_fields}
        if payload.get("blocker") != expected_blocker:
            raise SystemExit(
                "aggregated annotation-gap blocker differs from its sealed "
                f"group JSON source: {group_id}"
            )
        if (
            source.get("markdown") != record.get("markdown")
            or source.get("json") != record.get("json")
        ):
            raise SystemExit(
                "aggregated annotation-gap source paths changed: " + group_id
            )
        sources.append(source)
        payloads.append(payload)
    return sources, payloads, records


def _current_annotation_attempt(state: dict[str, Any]) -> dict[str, Any]:
    session = state.get("annotation_session")
    if not isinstance(session, dict) or not session.get("current_attempt"):
        raise SystemExit("the run has no persistent annotation agent session")
    attempt = state.get("attempts", {}).get(str(session["current_attempt"]))
    if not isinstance(attempt, dict) or attempt.get("phase") != "annotation":
        raise SystemExit(
            "persistent annotation session does not reference an annotation attempt"
        )
    return attempt


def retry_round(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    existing_retry = next(
        (
            attempt
            for attempt in reversed(list(state.get("attempts", {}).values()))
            if isinstance(attempt, dict)
            and attempt.get("phase") == args.phase
            and attempt.get("retry_reason") == args.reason
            and attempt.get("retry_previous_attempt") == args.previous_attempt
            and attempt.get("status") not in {"stale", "superseded"}
        ),
        None,
    )
    if isinstance(existing_retry, dict):
        print(
            json.dumps(
                {
                    "status": "already-retried",
                    "attempt": existing_retry["attempt_id"],
                    "previous_attempt": args.previous_attempt,
                },
                indent=2,
            )
        )
        return 0
    retry_is_authorized = any(
        isinstance(action, dict)
        and action.get("kind") == "main-owned-action"
        and action.get("action") == "retry-round"
        and action.get("phase") == args.phase
        and action.get("reason") == args.reason
        and action.get("previous_attempt") == args.previous_attempt
        for action in state.get("next_actions", [])
    )
    if not retry_is_authorized:
        raise SystemExit(
            "retry-round invocation does not match the current controller action"
        )
    running_deliveries = _running_deliveries(state)
    if running_deliveries:
        raise SystemExit(
            "cannot retry a round while an agent delivery is still running: "
            + ", ".join(item["attempt_id"] for item in running_deliveries)
        )
    feedback_sources: list[dict[str, str]] = []
    feedback_payloads: list[dict[str, Any]] = []
    annotation_gap_records: list[dict[str, Any]] = []
    annotation_causal_retry_count = 0
    if args.phase == "annotation":
        previous = _current_annotation_attempt(state)
        after_snapshot_errors = _annotation_after_snapshot_errors(state, previous)
        if after_snapshot_errors:
            # A retry handoff may cite a downstream report, but it still rests
            # on the currently accepted annotation provenance.  Convert drift
            # into an explicit terminal blocker instead of repeatedly raising
            # while the same controller-owned retry action remains pending.
            blocker = {
                "failure_class": "annotation-history-artifact-drift",
                "attempt_id": str(previous["attempt_id"]),
                "first_error": after_snapshot_errors[0],
                "error_count": len(after_snapshot_errors),
            }
            state["current_blockers"] = [blocker]
            state["next_actions"] = []
            _append_event(
                run_root,
                state,
                "annotation-history-artifact-drift",
                attempt_id=previous["attempt_id"],
            )
            _save_state(run_root, state)
            print(json.dumps({"status": "blocked", "blocker": blocker}, indent=2))
            return 1
        (
            feedback_sources,
            feedback_payloads,
            annotation_gap_records,
        ) = _feedback_sources_for_retry(state, args.previous_attempt)
        if any(
            feedback["attempt_id"] == previous["attempt_id"]
            for feedback in feedback_sources
        ):
            previous["status"] = "superseded"
            previous.setdefault("finished_at", _utc())
        annotation_causal_retry_count = _next_annotation_causal_retry_count(
            previous,
            feedback_payloads,
        )
    else:
        previous = _find_round_attempt(state, args.previous_attempt)
        if previous is None or previous.get("phase") != args.phase:
            raise SystemExit("previous attempt does not match retry phase")
        previous["status"] = "superseded"
        previous.setdefault("finished_at", _utc())
        try:
            feedback_payloads = [
                _json_load(_attempt_artifact(state, previous, "report"), {})
            ]
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            feedback_payloads = [{}]
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
        "report": str(_attempt_artifact(state, previous, "report")),
        "output": str(_attempt_artifact(state, previous, "output")),
        "reuse_policy": "read-only-reference",
    }
    lessons: list[dict[str, Any]] = []
    if annotation_gap_records:
        lessons.extend(
            {
                "must_address": "Aggregated group annotation gap: "
                + json.dumps(record, sort_keys=True)
            }
            for record in annotation_gap_records
        )
    else:
        for feedback_payload in feedback_payloads:
            result_blocker = feedback_payload.get("blocker")
            if isinstance(result_blocker, dict):
                lessons.append(
                    {"must_address": json.dumps(result_blocker, sort_keys=True)}
                )
    if args.phase == "vc-checking":
        # A fresh vc-checking agent has no parent transcript. Transfer the
        # controller-owned parent/merge failure into its sealed handoff before
        # downstream invalidation clears the run-level pointer. This is not
        # attributed to the previous (usually successful) owner report.
        for item in (
            state.get("current_blockers", [])
            if isinstance(state.get("current_blockers"), list)
            else []
        ):
            lessons.append(
                {
                    "must_address": "Controller failure evidence: "
                    + json.dumps(item, sort_keys=True)
                }
            )
    if "stale" in args.reason:
        # Owner reports do not need to duplicate controller version evidence.
        # Preserve the receipt recorded at detection; recomputation is only
        # supplemental because files may have been restored before this queued
        # transition is invoked.
        saved_receipts = [
            item
            for item in state.get("current_blockers", [])
            if isinstance(item, dict)
            and item.get("failure_class") == "current-version-drift"
        ]
        if not saved_receipts:
            found = _find_group_attempt(state, args.previous_attempt)
            if found is not None:
                proving, group_id = found
                receipt = (
                    proving.get("groups", {}).get(group_id, {}).get("version_drift")
                )
                if isinstance(receipt, dict):
                    saved_receipts.append(receipt)
        lessons.extend(
            {
                "must_address": "Controller version drift receipt: "
                + json.dumps(item, sort_keys=True)
            }
            for item in saved_receipts
        )
        saved_messages = {str(item.get("message") or "") for item in saved_receipts}
        lessons.extend(
            {"must_address": f"Current version drift check: {message}"}
            for message in _current_version_errors(state)
            if message not in saved_messages
        )
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
        annotation_causal_retry_count=annotation_causal_retry_count,
    )
    attempt["retry_reason"] = args.reason
    attempt["retry_previous_attempt"] = args.previous_attempt
    _append_event(
        run_root,
        state,
        "round-retried",
        phase=args.phase,
        previous=args.previous_attempt,
        reason=args.reason,
        annotation_session=(
            state["annotation_session"]["session_id"]
            if args.phase == "annotation"
            and isinstance(state.get("annotation_session"), dict)
            else None
        ),
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": attempt["status"],
                "attempt": attempt["attempt_id"],
                "action": state["next_actions"][0].get(
                    "action", state["next_actions"][0]["kind"]
                ),
            },
            indent=2,
        )
    )
    return 0
