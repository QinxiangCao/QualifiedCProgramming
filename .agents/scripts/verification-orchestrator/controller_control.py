"""Explicit pause, cancellation, and resume control for verification runs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from controller_state import (
    _append_event,
    _load_state,
    _run_root_from_id,
    _save_state,
    _utc,
)
from path_utils import fixed_path_under, write_json

CONTROL_SIGNAL_FILE_NAME = "controller_control.json"
CONTROL_STATUSES = frozenset({"active", "paused"})


def _args_main_root(args: argparse.Namespace) -> Path:
    return (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )


def control_signal_path(state: dict[str, Any]) -> Path:
    """Return the one mutable cooperative-control signal for this run."""

    main_root = Path(str(state["main_root"]))
    report_root = fixed_path_under(
        Path(str(state["report_root"])),
        main_root,
        label="controller report root",
    )
    return fixed_path_under(
        report_root / CONTROL_SIGNAL_FILE_NAME,
        report_root,
        label="controller control signal",
    )


def run_control_record(state: dict[str, Any]) -> dict[str, Any]:
    """Normalize legacy states without mutating them."""

    value = state.get("run_control")
    if isinstance(value, dict) and value.get("status") in CONTROL_STATUSES:
        return value
    return {
        "status": "active",
        "pause_count": 0,
    }


def run_is_paused(state: dict[str, Any]) -> bool:
    return run_control_record(state).get("status") == "paused"


def run_control_errors(value: Any) -> list[str]:
    """Validate the optional durable run-control record."""

    if value is None:
        return []
    if not isinstance(value, dict):
        return ["run_control must be an object"]
    allowed = {
        "status",
        "pause_count",
        "updated_at",
        "reason",
        "paused_at",
        "resumed_at",
        "cancelled_action",
        "suspended_next_actions",
        "suspended_waiting_for",
    }
    errors: list[str] = []
    if set(value) - allowed:
        errors.append(
            "run_control contains unsupported fields: "
            + repr(sorted(set(value) - allowed))
        )
    if value.get("status") not in CONTROL_STATUSES:
        errors.append("run_control.status must be active or paused")
    pause_count = value.get("pause_count")
    if (
        isinstance(pause_count, bool)
        or not isinstance(pause_count, int)
        or pause_count < 0
    ):
        errors.append("run_control.pause_count must be a non-negative integer")
    for field in ("updated_at", "reason", "paused_at", "resumed_at", "cancelled_action"):
        if field in value and (
            not isinstance(value[field], str) or not str(value[field]).strip()
        ):
            errors.append(f"run_control.{field} must be a non-empty string")
    for field in ("suspended_next_actions", "suspended_waiting_for"):
        if field in value and not isinstance(value[field], list):
            errors.append(f"run_control.{field} must be a list")
    if value.get("status") == "paused" and not value.get("paused_at"):
        errors.append("paused run_control requires paused_at")
    return errors


def control_signal_requests_stop(path: Path) -> bool:
    """Fail closed when a present control signal is malformed or paused."""

    try:
        if not path.is_file():
            return False
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return True
    return not isinstance(payload, dict) or payload.get("status") != "active"


def _write_control_signal(state: dict[str, Any]) -> None:
    control = run_control_record(state)
    write_json(
        control_signal_path(state),
        {
            "run_id": str(state["run_id"]),
            "status": str(control["status"]),
            "updated_at": str(control.get("updated_at") or _utc()),
            **(
                {"reason": str(control["reason"])}
                if control.get("reason")
                else {}
            ),
            **(
                {"cancelled_action": str(control["cancelled_action"])}
                if control.get("cancelled_action")
                else {}
            ),
        },
    )


def _known_action_ids(state: dict[str, Any]) -> set[str]:
    actions = {
        str(item["id"])
        for item in state.get("next_actions", [])
        if isinstance(item, dict) and item.get("id")
    }
    for attempt in state.get("attempts", {}).values():
        if not isinstance(attempt, dict):
            continue
        delivery = attempt.get("delivery")
        if (
            attempt.get("status") == "running"
            and isinstance(delivery, dict)
            and delivery.get("action_id")
        ):
            actions.add(str(delivery["action_id"]))
        for group in (attempt.get("groups") or {}).values():
            delivery = group.get("delivery") if isinstance(group, dict) else None
            if (
                isinstance(group, dict)
                and group.get("status") == "running"
                and isinstance(delivery, dict)
                and delivery.get("action_id")
            ):
                actions.add(str(delivery["action_id"]))
    return actions


def _pause(
    args: argparse.Namespace,
    *,
    cancelled_action: str | None,
) -> int:
    main_root = _args_main_root(args)
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    if state.get("phase") == "done":
        raise SystemExit("a completed run cannot be paused or cancelled")
    if cancelled_action is not None and cancelled_action not in _known_action_ids(state):
        raise SystemExit(
            "cancel-action does not name a current or claimed action: "
            + cancelled_action
        )
    previous = run_control_record(state)
    if previous.get("status") == "paused":
        if cancelled_action and previous.get("cancelled_action") != cancelled_action:
            previous = dict(previous)
            previous["cancelled_action"] = cancelled_action
            previous["reason"] = str(args.reason).strip()
            previous["updated_at"] = _utc()
            state["run_control"] = previous
            _write_control_signal(state)
            _append_event(
                run_root,
                state,
                "controller-action-cancelled",
                action=cancelled_action,
                reason=previous["reason"],
            )
            _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "already-paused",
                    "run": state["run_id"],
                    "run_control": run_control_record(state),
                },
                indent=2,
            )
        )
        return 0

    now = _utc()
    reason = str(args.reason).strip()
    control: dict[str, Any] = {
        "status": "paused",
        "pause_count": int(previous.get("pause_count", 0)) + 1,
        "updated_at": now,
        "paused_at": now,
        "reason": reason,
        "suspended_next_actions": list(state.get("next_actions", [])),
        "suspended_waiting_for": list(state.get("waiting_for", [])),
    }
    if cancelled_action is not None:
        control["cancelled_action"] = cancelled_action
    state["run_control"] = control
    state["next_actions"] = []
    state["waiting_for"] = [
        {
            "phase": str(state.get("phase") or ""),
            "status": "paused",
            "reason": reason,
        }
    ]
    # Publish the cooperative signal before state persistence so an already
    # running child stops even if a concurrent state generation wins the CAS.
    _write_control_signal(state)
    event = (
        "controller-action-cancelled"
        if cancelled_action is not None
        else "controller-run-paused"
    )
    _append_event(
        run_root,
        state,
        event,
        reason=reason,
        **({"action": cancelled_action} if cancelled_action is not None else {}),
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "paused",
                "run": state["run_id"],
                "cancelled_action": cancelled_action,
                "reason": reason,
            },
            indent=2,
        )
    )
    return 0


def pause_run(args: argparse.Namespace) -> int:
    """Pause a run without changing its verification phase or evidence."""

    return _pause(args, cancelled_action=None)


def cancel_action(args: argparse.Namespace) -> int:
    """Request cooperative cancellation and leave the run explicitly paused."""

    action = str(args.action).strip()
    if not action:
        raise SystemExit("--action must be a non-empty current action id")
    return _pause(args, cancelled_action=action)


def resume_run(args: argparse.Namespace) -> int:
    """Resume a paused run without executing or advancing any action."""

    main_root = _args_main_root(args)
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous = run_control_record(state)
    if previous.get("status") != "paused":
        # Repair a signal-first pause that was interrupted before its state CAS.
        _write_control_signal(state)
        print(
            json.dumps(
                {"status": "already-active", "run": state["run_id"]},
                indent=2,
            )
        )
        return 0
    now = _utc()
    suspended_actions = previous.get("suspended_next_actions")
    suspended_waiting = previous.get("suspended_waiting_for")
    state["run_control"] = {
        "status": "active",
        "pause_count": int(previous.get("pause_count", 0)),
        "updated_at": now,
        "resumed_at": now,
    }
    if not state.get("next_actions") and isinstance(suspended_actions, list):
        state["next_actions"] = suspended_actions
    if isinstance(suspended_waiting, list):
        state["waiting_for"] = suspended_waiting
    _write_control_signal(state)
    _append_event(
        run_root,
        state,
        "controller-run-resumed",
        previous_reason=str(previous.get("reason") or ""),
        previous_cancelled_action=str(previous.get("cancelled_action") or ""),
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "active",
                "run": state["run_id"],
                "next_action_ids": [
                    str(item.get("id"))
                    for item in state.get("next_actions", [])
                    if isinstance(item, dict) and item.get("id")
                ],
            },
            indent=2,
        )
    )
    return 0


def require_active_run(args: argparse.Namespace) -> Path | None:
    """Refuse every mutating public workflow command while a run is paused."""

    if not getattr(args, "run", None):
        return None
    main_root = _args_main_root(args)
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    if run_is_paused(state):
        control = run_control_record(state)
        raise SystemExit(
            "verification run is paused; use resume-run explicitly before "
            f"executing {args.command}: {control.get('reason', 'no reason recorded')}"
        )
    return control_signal_path(state)
