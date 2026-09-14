#!/usr/bin/env python3
"""Controller-owned vc-proving preparation and mechanical merge verification.

Copy and merge mechanics live in focused vc-proving modules; this internal
module binds them to the current round and current main-root files.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from controller_attempts import (
    _attempt_for_round,
    _proving_manifest_errors,
    _public_helper_pool_errors,
    _transition_current_file_drift,
)
from controller_invocations import hydrate_actions
from controller_rounds import (
    VC_PROVING_PHASE,
    _accepted_group_ids,
    _proving_feedback_attempt_id,
    _sync_group_actions,
    _target_witnesses,
)
from controller_state import (
    _append_event,
    _file_digest,
    _generated_artifact_module_spellings_for_state,
    _json_load,
    _load_state,
    _run_root_from_id,
    _save_state,
    _utc,
    _validated_proving_attempt_paths,
    _validated_annotation_attempt_paths,
)
from init_vc_proving_round import create_base_manifest
from prepare_group_workers import (
    prepare_group_workers,
    resolve_group_workers_manifest,
)
from proof_manual_utils import manual_vc_index
from verify_group_results import verify_and_merge


def _priority_group_ids(state: dict, groups: list[dict]) -> list[str]:
    accepted = state["accepted_rounds"]["annotation"]
    annotation_attempt = state["attempts"][accepted["attempt_id"]]
    plan = _json_load(
        _validated_annotation_attempt_paths(state, annotation_attempt)["plan"],
        {},
    )
    priority_vcs = {
        name
        for comparison in plan["vc_comparisons"]
        for name in comparison["current"]
    }
    if not priority_vcs:
        return []
    manual = (
        Path(str(state["main_root"]))
        / str(state["target_files"]["proof_manual_file"])
    ).read_text(encoding="utf-8")
    vc_index = manual_vc_index(manual)
    priority_witnesses = {
        str(vc_index["by_name"][name]["parent"] or name)
        for name in priority_vcs
    }
    return [
        str(group["id"])
        for group in groups
        if priority_witnesses
        & {str(witness["name"]) for witness in group["witnesses"]}
    ]


def _stop_for_current_file_drift(
    *,
    run_root: Path,
    state: dict,
    attempt: dict,
    action: str,
    retry_reason: str | None = None,
) -> bool:
    """Persist the annotation-feedback transition on current-file drift."""

    feedback_attempt = _proving_feedback_attempt_id(state)
    errors = _transition_current_file_drift(
        state,
        attempt,
        action=action,
        feedback_attempt_id=feedback_attempt,
        retry_reason=retry_reason,
    )
    if not errors:
        return False
    _append_event(
        run_root,
        state,
        "vc-proving-file-drift",
        round=str(attempt["round"]),
        action=action,
        first_error=errors[0],
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "stale",
                "errors": errors,
                "next_actions": hydrate_actions(
                    state, state.get("next_actions", [])
                ),
            },
            indent=2,
        )
    )
    return True


def vc_proving_preparing(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, VC_PROVING_PHASE)
    try:
        attempt_paths = _validated_proving_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        raise SystemExit(f"vc-proving attempt path topology is invalid: {exc}") from exc
    if attempt.get("status") != "prepared":
        raise SystemExit("vc-proving-preparing attempt is not in prepared state")
    if _stop_for_current_file_drift(
        run_root=run_root,
        state=state,
        attempt=attempt,
        action="vc-proving-preparing",
    ):
        return 1
    public_helper_errors = _public_helper_pool_errors(state)
    if public_helper_errors:
        raise SystemExit(
            "vc-proving-preparing public helper pool integrity failed: "
            + "; ".join(public_helper_errors)
        )

    accepted_vc = state.get("accepted_rounds", {}).get("vc-checking", {})
    group_plan = Path(str(accepted_vc.get("group_plan") or ""))
    expected_plan_sha256 = str(accepted_vc.get("group_plan_sha256") or "")
    if (
        not group_plan.is_file()
        or not expected_plan_sha256
        or _file_digest(group_plan) != expected_plan_sha256
    ):
        raise SystemExit("accepted group_plan.json changed before vc-proving-preparing")

    target = state["target_files"]
    report_directory = attempt_paths["report_directory"]
    base_manifest = create_base_manifest(
        manual_file=main_root / target["proof_manual_file"],
        formal_case_lib=main_root / target["formal_case_lib"],
        main_root=main_root,
        run_root=run_root,
        round_report_directory=report_directory,
        vc_proving_round_id=args.round,
        goals=_target_witnesses(state),
    )
    groups = prepare_group_workers(
        base_manifest,
        group_plan_path=group_plan,
        force_groups=True,
        previous_proving_round=attempt.get("previous_proving_round"),
        dependency_snapshot_sha256=str(
            state["dune_preparation"]["snapshot_sha256"]
        ),
        expected_proof_manual=str(target["proof_manual_file"]),
        expected_formal_case_lib=str(target["formal_case_lib"]),
        expected_run_root=run_root,
        expected_round=str(attempt["round"]),
    )
    if _stop_for_current_file_drift(
        run_root=run_root,
        state=state,
        attempt=attempt,
        action="vc-proving-preparing post-check",
    ):
        return 1
    if _file_digest(group_plan) != expected_plan_sha256:
        raise SystemExit(
            "accepted group_plan.json changed while preparing group copies"
        )

    attempt["status"] = "groups-ready"
    attempt["base_manifest"] = str(base_manifest)
    attempt["group_workers_manifest"] = str(
        report_directory / "group_workers_manifest.json"
    )
    attempt["base_manifest_sha256"] = _file_digest(base_manifest)
    attempt["group_workers_manifest_sha256"] = _file_digest(
        Path(attempt["group_workers_manifest"])
    )
    attempt["groups"] = {
        str(group["id"]): {"status": "prepared", "attempt_index": 1}
        for group in groups
    }
    attempt["priority_group_ids"] = _priority_group_ids(state, groups)
    _sync_group_actions(state, attempt)
    _append_event(
        run_root,
        state,
        "vc-proving-prepared",
        round=args.round,
        group_count=len(groups),
        previous_proving_round=attempt.get("previous_proving_round"),
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "groups-ready",
                "group_workers_manifest": attempt["group_workers_manifest"],
                "previous_proving_round": attempt.get("previous_proving_round"),
                "next_actions": hydrate_actions(
                    state, state.get("next_actions", [])
                ),
            },
            indent=2,
        )
    )
    return 0


def vc_proving_verify(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, VC_PROVING_PHASE)
    try:
        attempt_paths = _validated_proving_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        raise SystemExit(f"vc-proving attempt path topology is invalid: {exc}") from exc
    if attempt.get("status") != "groups-ready":
        raise SystemExit("vc-proving-verify attempt is not in groups-ready state")
    if _stop_for_current_file_drift(
        run_root=run_root,
        state=state,
        attempt=attempt,
        action="vc-proving-verify",
        retry_reason="vc-proving-parent-verify-stale",
    ):
        return 1
    public_helper_errors = _public_helper_pool_errors(state)
    if public_helper_errors:
        raise SystemExit(
            "vc-proving-verify public helper pool integrity failed: "
            + "; ".join(public_helper_errors)
        )
    integrity_errors = _proving_manifest_errors(state, attempt)
    if integrity_errors:
        raise SystemExit(
            "vc-proving manifest integrity failed: " + "; ".join(integrity_errors)
        )
    manifest = resolve_group_workers_manifest(
        attempt_paths["group_workers_manifest"],
        main_root=main_root,
        expected_run_root=run_root,
        expected_round=str(attempt["round"]),
    )
    base = _json_load(attempt_paths["base_manifest"], {})
    target = state["target_files"]
    if (
        base.get("proof_manual") != target["proof_manual_file"]
        or base.get("formal_case_lib") != target["formal_case_lib"]
    ):
        raise SystemExit(
            "vc-proving base manifest does not match current target formal paths"
        )
    group_ids = {str(group["id"]) for group in manifest.get("groups", [])}
    _sync_group_actions(state, attempt)
    accepted = _accepted_group_ids(attempt)
    if accepted != group_ids:
        _save_state(run_root, state)
        raise SystemExit(
            f"vc-proving-verify requires all groups accepted: missing {sorted(group_ids - accepted)}"
        )
    result = verify_and_merge(
        attempt_paths["group_workers_manifest"],
        main_root=main_root,
        goal_check_file=Path(str(target["goal_check_file"])),
        expected_run_root=run_root,
        expected_round=str(attempt["round"]),
        forbidden_modules=_generated_artifact_module_spellings_for_state(
            state,
        ),
    )
    if _stop_for_current_file_drift(
        run_root=run_root,
        state=state,
        attempt=attempt,
        action="vc-proving-verify post-check",
        retry_reason="vc-proving-parent-verify-stale",
    ):
        return 1
    post_integrity_errors = _proving_manifest_errors(state, attempt)
    _sync_group_actions(state, attempt)
    post_accepted = _accepted_group_ids(attempt)
    if post_integrity_errors or post_accepted != group_ids:
        raise SystemExit(
            "vc-proving inputs changed during parent verification: "
            + (
                post_integrity_errors[0]
                if post_integrity_errors
                else f"accepted groups changed: {sorted(group_ids - post_accepted)}"
            )
        )
    if result.get("status") != "passed":
        attempt["status"] = "parent-verify-failed"
        attempt["finished_at"] = _utc()
        attempt["proving_merged_result"] = str(
            Path(str(attempt["report_directory"])) / "proving_merged_result.json"
        )
        attempt["failure_status"] = "parent-verify-failed"
        attempt["failed_result_sha256"] = _file_digest(
            Path(attempt["proving_merged_result"])
        )
        first_failure = (
            result.get("failure")
            if isinstance(result.get("failure"), dict)
            else {
                "category": "proof-route",
                "kind": "parent-verification-failed",
                "message": "parent verification failed",
            }
        )
        blockers = [
            {
                "failure_class": "proving-merged-parent-verify",
                "first_failure": first_failure,
                "error_count": int(result.get("error_count", 0)),
                "blocker_count": int(result.get("blocker_count", 0)),
                "proving_merged_result": attempt["proving_merged_result"],
                "proving_merged_result_sha256": attempt["failed_result_sha256"],
            }
        ]
        state["current_blockers"] = blockers
        retry_phase = "vc-checking" if _target_witnesses(state) else "annotation"
        state["next_actions"] = [
            {
                "id": f"{retry_phase}-retry-{args.round}",
                "kind": "main-owned-action",
                "action": "retry-round",
                "phase": retry_phase,
                "reason": "vc-proving-parent-failed",
                "previous_attempt": _proving_feedback_attempt_id(state),
            }
        ]
        _append_event(
            run_root,
            state,
            "vc-proving-verify-failed",
            round=args.round,
            error_count=int(result.get("error_count", 0)),
            proving_merged_result=attempt["proving_merged_result"],
        )
        _save_state(run_root, state)
        print(json.dumps({"status": "failed", "blockers": blockers}, indent=2))
        return 1
    attempt["status"] = "verified"
    attempt["finished_at"] = _utc()
    attempt["proving_merged_result"] = str(
        Path(str(attempt["report_directory"])) / "proving_merged_result.json"
    )
    attempt["verified_result_sha256"] = _file_digest(
        Path(attempt["proving_merged_result"])
    )
    state["accepted_rounds"][VC_PROVING_PHASE] = {
        "round": args.round,
        "attempt_id": attempt["attempt_id"],
        "result_sha256": attempt["verified_result_sha256"],
    }
    candidate = result["candidate"]
    state["final_candidate"] = {
        "round": args.round,
        "proving_merged_result": attempt["proving_merged_result"],
        "result_sha256": attempt["verified_result_sha256"],
        "proof_manual_sha256": candidate.get("proof_manual_sha256"),
        "proving_merged_lib_sha256": candidate.get(
            "proving_merged_lib_sha256"
        ),
    }
    state["phase"] = "final-candidate-apply"
    state["next_actions"] = [
        {
            "id": "final-candidate-apply",
            "kind": "main-owned-action",
            "action": "final-apply",
        }
    ]
    _append_event(run_root, state, "vc-proving-verified", round=args.round)
    _save_state(run_root, state)
    response = {
        "status": "verified",
        "proving_merged_result": attempt["proving_merged_result"],
    }
    if candidate.get("proof_manual_sha256") is not None:
        response["proof_manual"] = target["proof_manual_file"]
    if candidate.get("proving_merged_lib_sha256") is not None:
        response["formal_case_lib"] = target["formal_case_lib"]
    print(json.dumps(response, indent=2))
    return 0
