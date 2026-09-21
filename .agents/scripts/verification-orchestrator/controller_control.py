"""Pause/resume one run. Its tasks stay intact; actions are derived on demand."""
from __future__ import annotations

import json
from pathlib import Path

from controller_state import _append_event, _save_state, _utc, load_run
from path_utils import fixed_path_under, write_json


def control_signal_path(state: dict) -> Path:
    root = Path(state["report_root"])
    return fixed_path_under(root / "controller_control.json", root, label="run control signal")


def run_control_record(state: dict) -> dict:
    return state["run_control"]


def run_is_paused(state: dict) -> bool:
    return state["run_control"]["status"] == "paused"


def _write_control_signal(state: dict) -> None:
    write_json(control_signal_path(state), {"run_id": state["run_id"], **state["run_control"]})


def _pause(args, action: str | None) -> int:
    from controller_rounds import derive_actions
    reason = args.reason.strip()
    if not reason:
        raise SystemExit("pause reason must be non-empty")
    state = load_run(args)
    if state["phase"] == "done":
        raise SystemExit("a completed run cannot be paused")
    if action is not None:
        known = {item["id"] for item in derive_actions(state)}
        for task in state["attempts"].values():
            known.update(record.get("claimed_action") for record in [task, *task.get("groups", {}).values()]
                         if record["status"] in {"running", "returned"})
        if action not in known and action != state["run_control"].get("cancelled_action"):
            raise SystemExit("cancel-action does not name a current or claimed action")
    control = state["run_control"]
    already = control["status"] == "paused"
    control.update(status="paused", reason=reason, updated_at=_utc(),
                   pause_count=control.get("pause_count", 0) + int(not already))
    if action is not None:
        control["cancelled_action"] = action
    _write_control_signal(state)
    _save_state(Path(state["run_root"]), state)
    _append_event(Path(state["run_root"]), state, "paused", reason=reason, action=action)
    print(json.dumps({"status": "already-paused" if already else "paused", "reason": reason,
                      "run": state["run_id"]}, indent=2))
    return 0


def pause_run(args) -> int:
    return _pause(args, None)


def cancel_action(args) -> int:
    return _pause(args, args.action)


def resume_run(args) -> int:
    from controller_rounds import derive_actions
    state = load_run(args)
    control = state["run_control"]
    already = control["status"] == "active"
    state["run_control"] = {"status": "active", "updated_at": _utc(), "pause_count": control.get("pause_count", 0)}
    _write_control_signal(state)
    _save_state(Path(state["run_root"]), state)
    _append_event(Path(state["run_root"]), state, "resumed")
    print(json.dumps({"status": "already-active" if already else "active", "run": state["run_id"],
                      "next_actions": derive_actions(state)}, indent=2))
    return 0


def require_active_run(args) -> Path | None:
    if not getattr(args, "run", None):
        return None
    state = load_run(args)
    if run_is_paused(state):
        raise SystemExit(f"verification run is paused: {state['run_control'].get('reason', '')}")
    return control_signal_path(state)
