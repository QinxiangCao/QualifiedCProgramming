"""Prepare the current case's native dependencies, then select its next role."""
from __future__ import annotations

import json
from pathlib import Path
from controller_state import _current_files_errors, _load_state, _manual_obligations, _save_state, load_run
from coq_tooling import compact_dune_preparation, dependency_snapshot_file_name, prepare_dune_dependencies
from path_utils import write_json


def dune_build(args) -> int:
    from controller_rounds import derive_actions, new_attempt, require_action
    state = load_run(args)
    require_action(state, "dune-build")
    errors = _current_files_errors(state)
    if errors:
        state["pending_retry"] = {"phase": "annotation", "reason": "current-file-drift",
                                  "previous_attempt": state["current"]["annotation"]}
        state["current_blockers"] = [{"failure_class": "current-file-drift", "message": errors[0]}]
        _save_state(Path(state["run_root"]), state)
        result = {"status": "failed", "errors": errors}
    else:
        root = Path(state["main_root"])
        result = prepare_dune_dependencies(
            workspace_root=root, target_file=Path(state["target_files"]["goal_check_file"]),
            current_case_anchor=Path(state["target_files"]["proof_auto_file"]),
            snapshot_path=Path(state["run_root"]) / dependency_snapshot_file_name(root))
        fresh = _load_state(Path(state["run_root"]))
        if fresh["generation"] != state["generation"] or fresh["run_control"]["status"] == "paused":
            print(json.dumps({"status": "interrupted", "next_actions": derive_actions(fresh)}))
            return 1
        state["dune_preparation"] = compact_dune_preparation(result)
        if result["status"] == "passed":
            if _manual_obligations(state)["top_level"]:
                new_attempt(state, "vc-checking")
            else:
                write_json(Path(state["report_root"]) / "group_plan.json", {"groups": []})
                new_attempt(state, "vc-proving")
        # A native build failure leaves this exact preparation action available.
        _save_state(Path(state["run_root"]), state)
    print(json.dumps({**compact_dune_preparation(result), "phase": state["phase"],
                      "next_actions": derive_actions(state)}, indent=2))
    return 0 if result["status"] == "passed" else 1
