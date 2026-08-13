#!/usr/bin/env python3
"""Controller-owned selected-backend preparation between annotation and VC work."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from controller_invocations import hydrate_actions
from controller_state import (
    _append_event,
    _current_version_errors,
    _load_state,
    _run_root_from_id,
    _save_state,
)
from coq_tooling import (
    DUNE_BUILD_MODE,
    compact_dune_preparation,
    dependency_snapshot_file_name,
    detect_build_mode,
    prepare_dune_dependencies,
)


def _preparation_action(state: dict[str, Any]) -> dict[str, Any]:
    """Return the sole action that seals the selected backend's accepted graph."""

    return {
        "id": "dune-build",
        "kind": "main-owned-action",
        "action": "dune-build",
        "source_goal_version": str(
            (state.get("source_goal_version") or {}).get("digest") or ""
        ),
    }


def _queue_annotation_retry_for_drift(
    state: dict[str, Any], errors: list[str], *, build_mode: str
) -> None:
    build_label = (
        "Dune build"
        if build_mode == DUNE_BUILD_MODE
        else "Makefile preparation"
    )
    repair_label = "Dune" if build_mode == DUNE_BUILD_MODE else "Makefile"
    accepted = state.get("accepted_rounds", {}).get("annotation", {})
    attempt_id = str(accepted.get("attempt_id") or "")
    if not attempt_id:
        raise SystemExit(
            f"{build_label} source drift has no accepted annotation feedback source"
        )
    receipt = {
        "status": "stale",
        "source_goal_version": str(
            (state.get("source_goal_version") or {}).get("digest") or ""
        ),
        "first_failure": {
            "category": "freshness",
            "kind": (
                "dune-source-drift"
                if build_mode == DUNE_BUILD_MODE
                else "makefile-source-drift"
            ),
            "message": errors[0],
            "repair": (
                "Return through the existing annotation retry and rebuild the exact "
                f"accepted source with {repair_label}."
            ),
        },
    }
    state["dune_preparation"] = receipt
    state["current_blockers"] = [receipt["first_failure"]]
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


def dune_build(args: argparse.Namespace) -> int:
    """Prepare the exact goal-check and seal its fixed dependency snapshot."""

    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    build_mode = detect_build_mode(main_root)
    build_label = (
        "Dune build"
        if build_mode == DUNE_BUILD_MODE
        else "Makefile preparation"
    )
    state = _load_state(run_root)
    if state.get("phase") not in {"annotation", "dune-build"}:
        raise SystemExit(
            f"{build_label} is only valid after annotation acceptance and before "
            "vc-checking"
        )

    accepted = state.get("accepted_rounds", {}).get("annotation", {})
    source_goal = state.get("source_goal_version")
    source_goal_digest = str(
        source_goal.get("digest") if isinstance(source_goal, dict) else ""
    )
    if (
        not isinstance(accepted, dict)
        or not source_goal_digest
        or accepted.get("source_goal_version") != source_goal_digest
    ):
        raise SystemExit(
            f"{build_label} requires the current accepted annotation "
            "source_goal_version"
        )

    version_errors = _current_version_errors(state)
    if version_errors:
        _queue_annotation_retry_for_drift(
            state, version_errors, build_mode=build_mode
        )
        _append_event(
            run_root,
            state,
            "dune-preparation-stale",
            first_error=version_errors[0],
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "stale",
                    "errors": version_errors,
                    "next_actions": hydrate_actions(
                        state, state.get("next_actions", [])
                    ),
                },
                indent=2,
            )
        )
        return 1

    state["phase"] = "dune-build"
    _append_event(
        run_root,
        state,
        "dune-preparation-started",
        source_goal_version=source_goal_digest,
    )
    _save_state(run_root, state)

    evidence = prepare_dune_dependencies(
        workspace_root=main_root,
        target_file=Path(str(state["target_files"]["goal_check_file"])),
        current_case_anchor=Path(
            str(state["target_files"]["proof_auto_file"])
        ),
        source_goal_version=source_goal_digest,
        snapshot_path=run_root / dependency_snapshot_file_name(main_root),
    )

    # Preparation may take long enough for an accidental edit to invalidate
    # the accepted annotation. Recheck before publishing the receipt.
    state = _load_state(run_root)
    version_errors = _current_version_errors(state)
    if version_errors:
        _queue_annotation_retry_for_drift(
            state, version_errors, build_mode=build_mode
        )
        _append_event(
            run_root,
            state,
            "dune-preparation-stale",
            first_error=version_errors[0],
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "stale",
                    "errors": version_errors,
                    "next_actions": hydrate_actions(
                        state, state.get("next_actions", [])
                    ),
                },
                indent=2,
            )
        )
        return 1

    receipt = compact_dune_preparation(evidence)
    state["dune_preparation"] = receipt
    state["phase"] = "dune-build"
    if receipt.get("status") == "passed":
        state["current_blockers"] = []
        state["next_actions"] = []
        _append_event(
            run_root,
            state,
            "dune-preparation-passed",
            snapshot_digest=receipt.get("snapshot_sha256"),
            dependency_count=receipt.get("base_artifact_count"),
        )
        exit_code = 0
    else:
        failure = receipt.get("first_failure")
        if not isinstance(failure, dict):
            makefile_mode = receipt.get("build_mode") == "makefile"
            failure = {
                "category": "tooling",
                "kind": (
                    "makefile-build-failed"
                    if makefile_mode
                    else "dune-build-failed"
                ),
                "message": (
                    "Makefile preparation failed without structured evidence."
                    if makefile_mode
                    else "Dune preparation failed without structured evidence."
                ),
                "repair": "Repair the reported exact target build and rerun dune-build.",
            }
        state["current_blockers"] = [failure]
        state["next_actions"] = [_preparation_action(state)]
        _append_event(
            run_root,
            state,
            "dune-preparation-failed",
            failure=failure,
        )
        exit_code = 1

    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": receipt.get("status"),
                "dune_preparation": receipt,
                "next_actions": hydrate_actions(state, state.get("next_actions", [])),
            },
            indent=2,
        )
    )
    return exit_code
