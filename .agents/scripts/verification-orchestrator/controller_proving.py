"""Prepare current groups, then merge and compile their complete result."""
from __future__ import annotations

import json
from pathlib import Path

from controller_state import (
    _current_files_errors, _generated_artifact_module_spellings_for_state, _load_state,
    _save_state, _utc, attempt_paths, load_run, require_attempt,
)
from coq_tooling import run_coqc_check
from path_utils import fixed_path_under
from proving import load_proving_context, merge_groups, prepare_groups


def _context(state: dict, task: dict):
    source_id = task.get("source_vc_checking")
    plan = (attempt_paths(state, state["attempts"][source_id])["group_plan"] if source_id
            else Path(state["report_root"]) / "group_plan.json")
    from controller_rounds import previous_proving_round
    return load_proving_context(
        main_root=Path(state["main_root"]), run_root=Path(state["run_root"]), round_id=task["attempt_id"],
        group_plan_path=plan, proof_manual=Path(state["target_files"]["proof_manual_file"]),
        formal_case_lib=Path(state["target_files"]["formal_case_lib"]),
        previous_round=previous_proving_round(state, task),
        forbidden_modules=_generated_artifact_module_spellings_for_state(state),
    )


def _respond(state: dict, result: dict) -> int:
    from controller_rounds import derive_actions, waiting
    print(json.dumps({**result, "phase": state["phase"], "next_actions": derive_actions(state),
                      "waiting_for": waiting(state)}, indent=2))
    return 0 if result.get("status") == "passed" else 1


def _drift(state: dict, task: dict) -> list[str]:
    errors = _current_files_errors(state)
    if errors:
        state["pending_retry"] = {"phase": "annotation", "reason": "current-file-drift", "previous_attempt": task["attempt_id"]}
        state["current_blockers"] = [{"failure_class": "current-file-drift", "message": errors[0]}]
    return errors


def vc_proving_preparing(args) -> int:
    from controller_rounds import require_action
    state = load_run(args)
    require_action(state, "vc-proving-preparing", round=args.round)
    task = require_attempt(state, args.round, "vc-proving")
    errors = _drift(state, task)
    if errors:
        result = {"status": "failed", "errors": errors}
    else:
        groups = prepare_groups(_context(state, task))
        task["groups"] = {group["id"]: {"status": "prepared", "owner": None, "claimed_action": None,
                                        "repair_index": 0, "created_at": _utc()} for group in groups}
        task["status"] = "running"
        result = {"status": "passed", "group_count": len(groups)}
    _save_state(Path(state["run_root"]), state)
    return _respond(state, result)


def vc_proving_verify(args) -> int:
    from controller_rounds import require_action
    state = load_run(args)
    require_action(state, "vc-proving-verify", round=args.round)
    task = require_attempt(state, args.round, "vc-proving")
    errors = _drift(state, task)
    if errors:
        _save_state(Path(state["run_root"]), state)
        return _respond(state, {"status": "failed", "errors": errors})
    context = _context(state, task)
    result = merge_groups(context)
    if result["status"] == "passed":
        overlays = {Path(state["target_files"][role]): Path(result["candidate"][field])
                    for role, field in (("proof_manual_file", "proof_manual"), ("formal_case_lib", "formal_case_lib"))
                    if result["candidate"][field] is not None}
        checked = run_coqc_check(
            workspace_root=Path(state["main_root"]),
            build_workspace=Path(state["run_root"]) / "_coq_builds" / task["attempt_id"] / "parent" / "src",
            target_file=Path(state["target_files"]["goal_check_file"]), target_kind="parent",
            current_case_anchor=Path(state["target_files"]["proof_auto_file"]), overlays=overlays,
        )
        result["coq_check"] = checked
        result["status"] = checked["status"]
    fresh = _load_state(Path(state["run_root"]))
    if fresh["generation"] != state["generation"] or fresh["run_control"]["status"] == "paused":
        return _respond(fresh, {"status": "interrupted"})
    if result.get("group_errors"):
        from controller_rounds import render_handoff
        for group_id, errors in result["group_errors"].items():
            record = task["groups"][group_id]
            record.update(status="prepared", repair_index=record.get("repair_index", 0) + 1,
                          claimed_action=None, feedback="\n".join(errors))
            record.pop("finished_at", None)
            render_handoff(state, task, group_id=group_id)
        state["current_blockers"] = []
    elif result["status"] == "passed":
        task.update(status="accepted", finished_at=_utc())
        state.update(phase="final-apply", final_candidate={"round": task["attempt_id"]}, current_blockers=[])
    else:
        # A failed combination is reviewed by the existing VC owner workflow.
        task.update(status="blocked", blocker={"failure_class": "parent-check", "message": str(result)})
        state["pending_retry"] = {"phase": "vc-checking" if task.get("source_vc_checking") else "annotation",
                                  "reason": "parent-check-failed", "previous_attempt": task["attempt_id"]}
        state["current_blockers"] = [{"failure_class": "parent-check", "message": str(result)}]
    _save_state(Path(state["run_root"]), state)
    return _respond(state, result)
