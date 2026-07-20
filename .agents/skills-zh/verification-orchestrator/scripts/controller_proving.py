#!/usr/bin/env python3
"""Controller-owned vc-proving preparation and mechanical merge verification.

Copy and merge mechanics live in focused vc-proving modules; this internal
module binds them to the current round and source_goal_version.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from init_vc_proving_round import create_base_manifest
from prepare_group_workers import prepare_group_workers
from verify_group_results import verify_and_merge

from controller_state import (
    _append_event,
    _current_version_errors,
    _file_digest,
    _json_load,
    _load_state,
    _run_root_from_id,
    _save_state,
    _utc,
)
from controller_attempts import _attempt_for_round, _proving_manifest_errors
from controller_rounds import VC_PROVING_PHASE, _sync_group_actions


def _require_current_versions(state: dict, action: str) -> None:
    errors = _current_version_errors(state)
    if errors:
        raise SystemExit(f"{action} requires current accepted annotation files: {'; '.join(errors)}")


def vc_proving_preparing(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, VC_PROVING_PHASE)
    if attempt.get("status") != "prepared":
        raise SystemExit("vc-proving-preparing attempt is not in prepared state")
    _require_current_versions(state, "vc-proving-preparing")
    source_goal = state.get("source_goal_version")
    if not isinstance(source_goal, dict) or not source_goal.get("digest"):
        raise SystemExit("vc-proving-preparing requires current source_goal_version")
    if attempt.get("source_goal_version") != source_goal.get("digest"):
        raise SystemExit("vc-proving-preparing attempt source_goal_version is stale")
    accepted_vc = state.get("accepted_rounds", {}).get("vc-checking", {})
    if accepted_vc.get("source_goal_version") != source_goal.get("digest"):
        raise SystemExit("accepted vc-checking round source_goal_version is stale")
    target = state["target_files"]
    report_directory = Path(str(attempt["report_directory"]))
    base_manifest = create_base_manifest(
        manual_file=main_root / target["proof_manual_file"],
        formal_case_lib=main_root / target["formal_case_lib"],
        main_root=main_root,
        run_root=run_root,
        round_report_directory=report_directory,
        vc_proving_round_id=args.round,
        source_goal_version=str(source_goal["digest"]),
    )
    group_plan = Path(str(state["accepted_rounds"]["vc-checking"]["group_plan"]))
    groups = prepare_group_workers(
        base_manifest,
        group_plan_path=group_plan,
        force_groups=True,
        max_compact_attempts=state["max_compact_attempts"],
    )
    attempt["status"] = "groups-ready"
    attempt["base_manifest"] = str(base_manifest)
    attempt["group_workers_manifest"] = str(report_directory / "group_workers_manifest.json")
    attempt["base_manifest_sha256"] = _file_digest(base_manifest)
    attempt["group_workers_manifest_sha256"] = _file_digest(Path(attempt["group_workers_manifest"]))
    attempt["groups"] = {str(group["id"]): {"status": "prepared", "attempt_index": 1} for group in groups}
    state["accepted_groups"][args.round] = []
    _sync_group_actions(state, attempt)
    _append_event(
        run_root,
        state,
        "vc-proving-prepared",
        round=args.round,
        group_count=len(groups),
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "groups-ready",
                "group_workers_manifest": attempt["group_workers_manifest"],
                "next_actions": state["next_actions"],
            },
            indent=2,
        )
    )
    return 0


def vc_proving_verify(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, VC_PROVING_PHASE)
    _require_current_versions(state, "vc-proving-verify")
    integrity_errors = _proving_manifest_errors(attempt)
    if integrity_errors:
        raise SystemExit("vc-proving manifest integrity failed: " + "; ".join(integrity_errors))
    manifest = _json_load(Path(str(attempt["group_workers_manifest"])), {})
    base = _json_load(Path(str(attempt["base_manifest"])), {})
    target = state["target_files"]
    if (
        base.get("proof_manual") != target["proof_manual_file"]
        or base.get("formal_case_lib") != target["formal_case_lib"]
    ):
        raise SystemExit("vc-proving base manifest does not match current target formal paths")
    group_ids = {str(group["id"]) for group in manifest.get("groups", [])}
    accepted = set(state.get("accepted_groups", {}).get(args.round, []))
    if accepted != group_ids:
        raise SystemExit(f"vc-proving-verify requires all groups accepted: missing {sorted(group_ids - accepted)}")
    result = verify_and_merge(Path(str(attempt["group_workers_manifest"])), main_root=main_root)
    if result.get("status") != "passed":
        attempt["status"] = "parent-verify-failed"
        attempt["finished_at"] = _utc()
        attempt["proving_merged_result"] = str(Path(str(attempt["report_directory"])) / "proving_merged_result.json")
        blockers = [
            {
                "failure_class": "proving-merged-parent-verify",
                "errors": result.get("errors", []),
                "blockers": result.get("blockers", []),
                "proving_merged_result": attempt["proving_merged_result"],
            }
        ]
        state["current_blockers"] = blockers
        state["next_actions"] = [
            {
                "id": f"vc-proving-verify-{args.round}",
                "kind": "main-owned-action",
                "action": "vc-proving-verify",
                "round": args.round,
                "attempt_id": args.round,
            }
        ]
        _append_event(
            run_root,
            state,
            "vc-proving-verify-failed",
            round=args.round,
            error_count=len(result.get("errors", [])),
            proving_merged_result=attempt["proving_merged_result"],
        )
        _save_state(run_root, state)
        print(json.dumps({"status": "failed", "blockers": blockers}, indent=2))
        return 1
    attempt["status"] = "verified"
    attempt["finished_at"] = _utc()
    attempt["proving_merged_result"] = str(Path(str(attempt["report_directory"])) / "proving_merged_result.json")
    state["accepted_rounds"][VC_PROVING_PHASE] = {
        "round": args.round,
        "directory": attempt["directory"],
        "group_workers_manifest": attempt["group_workers_manifest"],
        "proving_merged_result": attempt["proving_merged_result"],
        "source_goal_version": state["source_goal_version"]["digest"],
    }
    state["final_candidate"] = {
        "source_goal_version": state["source_goal_version"]["digest"],
        "proof_manual": result["candidate"]["proof_manual"],
        "proving_merged_lib": result["candidate"]["proving_merged_lib"],
        "proof_manual_sha256": result["candidate"]["proof_manual_sha256"],
        "proving_merged_lib_sha256": result["candidate"]["proving_merged_lib_sha256"],
        "formal_proof_manual_relative": result["candidate"]["formal_proof_manual_relative"],
        "formal_case_lib_relative": result["candidate"]["formal_case_lib_relative"],
        "proving_merged_result": attempt["proving_merged_result"],
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
    print(
        json.dumps(
            {
                "status": "verified",
                "proving_merged_result": attempt["proving_merged_result"],
                "proof_manual": result["candidate"]["formal_proof_manual_relative"],
                "formal_case_lib": result["candidate"]["formal_case_lib_relative"],
            },
            indent=2,
        )
    )
    return 0
