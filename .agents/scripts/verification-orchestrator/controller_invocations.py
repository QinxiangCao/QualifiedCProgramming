#!/usr/bin/env python3
"""Derive public controller invocations and agent handoffs from compact state."""

from __future__ import annotations

import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

DELIVERY_ACTION_KINDS = frozenset(
    {
        "spawn-attempt",
        "spawn-group-worker",
        "append-group-worker",
        "spawn-annotation-agent",
        "append-annotation-agent",
    }
)


def _main_root(state: dict[str, Any]) -> Path:
    root = Path(str(state["main_root"])).expanduser().resolve()
    if not root.is_absolute():
        raise ValueError("controller state main_root must be absolute")
    return root


def _controller_path(state: dict[str, Any]) -> Path:
    return (
        _main_root(state)
        / ".agents"
        / "scripts"
        / "verification-orchestrator"
        / "controller.py"
    )


def invocation(
    state: dict[str, Any],
    command: str,
    *command_args: str,
) -> dict[str, Any]:
    """Return one complete, shell-free invocation for a run-scoped command."""

    root = _main_root(state)
    argv = [
        str(Path(sys.executable).expanduser().resolve()),
        str(_controller_path(state)),
        "--main-root",
        str(root),
        str(command),
        "--run",
        str(state["run_id"]),
        *(str(item) for item in command_args),
    ]
    return {"argv": argv, "cwd": str(root)}


def _required_action_value(action: dict[str, Any], key: str) -> str:
    value = str(action.get(key) or "")
    if not value:
        raise ValueError(
            f"main-owned action {action.get('id')} lacks required field {key}"
        )
    return value


def invocation_for_main_action(
    state: dict[str, Any], action: dict[str, Any]
) -> dict[str, Any]:
    command = _required_action_value(action, "action")
    arguments: list[str] = []
    if command in {
        "annotation-check-round",
        "vc-checking-check-round",
        "vc-proving-preparing",
        "vc-proving-verify",
    }:
        arguments.extend(["--round", _required_action_value(action, "round")])
        if command == "vc-checking-check-round" and action.get("group_plan"):
            arguments.extend(["--group-plan", str(action["group_plan"])])
    elif command == "annotation-summary-ready":
        arguments.extend(
            ["--attempt", _required_action_value(action, "attempt_id")]
        )
    elif command == "retry-round":
        arguments.extend(
            [
                "--phase",
                _required_action_value(action, "phase"),
                "--reason",
                _required_action_value(action, "reason"),
                "--previous-attempt",
                _required_action_value(action, "previous_attempt"),
            ]
        )
    elif command == "finalize-delivery":
        arguments.extend(
            [
                "--attempt",
                _required_action_value(action, "attempt_id"),
                "--owner",
                _required_action_value(action, "owner"),
            ]
        )
    elif command not in {
        "dune-build",
        "final-apply",
        "final-check",
    }:
        raise ValueError(f"unsupported main-owned controller action: {command}")
    return invocation(state, command, *arguments)


def role_for_delivery(action: dict[str, Any]) -> str:
    kind = str(action.get("kind") or "")
    if kind in {"spawn-annotation-agent", "append-annotation-agent"}:
        return "annotation-subagent"
    if kind == "spawn-attempt" and action.get("phase") == "vc-checking":
        return "vc-checking-subagent"
    if kind in {"spawn-group-worker", "append-group-worker"}:
        return "group-worker"
    raise ValueError(f"action is not a known agent delivery: {action.get('id')}")


def _claimed_owner(state: dict[str, Any], attempt_id: str) -> str | None:
    if ":" not in attempt_id:
        attempt = state.get("attempts", {}).get(attempt_id)
        if not isinstance(attempt, dict):
            return None
        delivery = attempt.get("delivery")
        if isinstance(delivery, dict) and delivery.get("owner"):
            return str(delivery["owner"])
        if attempt.get("owner"):
            return str(attempt["owner"])
        return None
    round_id, group_id = attempt_id.split(":", 1)
    attempt = state.get("attempts", {}).get(round_id)
    group = (
        attempt.get("groups", {}).get(group_id)
        if isinstance(attempt, dict)
        else None
    )
    if not isinstance(group, dict):
        return None
    delivery = group.get("delivery")
    if isinstance(delivery, dict) and delivery.get("owner"):
        return str(delivery["owner"])
    if group.get("owner"):
        return str(group["owner"])
    return None


def owner_for_delivery(
    state: dict[str, Any], action: dict[str, Any]
) -> str:
    attempt_id = _required_action_value(action, "attempt_id")
    existing = _claimed_owner(state, attempt_id)
    if existing:
        return existing
    kind = str(action.get("kind") or "")
    if kind in {"spawn-annotation-agent", "append-annotation-agent"}:
        session = state.get("annotation_session")
        if isinstance(session, dict) and session.get("owner"):
            return str(session["owner"])
        return f"annotation/{state['run_id']}"
    if kind == "spawn-attempt":
        return f"vc-checking/{attempt_id}"
    if kind in {"spawn-group-worker", "append-group-worker"}:
        round_id, separator, group_id = attempt_id.partition(":")
        if not separator or not round_id or not group_id:
            raise ValueError(f"invalid group delivery attempt id: {attempt_id}")
        return f"group-worker/{round_id}/{group_id}"
    raise ValueError(f"action is not an agent delivery: {action.get('id')}")


def claim_invocation(
    state: dict[str, Any], action: dict[str, Any]
) -> dict[str, Any]:
    owner = owner_for_delivery(state, action)
    return invocation(
        state,
        "claim-attempt",
        "--next-action",
        _required_action_value(action, "id"),
        "--owner",
        owner,
    )


def finalize_invocation(
    state: dict[str, Any], attempt_id: str, owner: str
) -> dict[str, Any]:
    if not attempt_id or not owner:
        raise ValueError("finalize invocation requires an attempt and owner")
    return invocation(
        state,
        "finalize-delivery",
        "--attempt",
        attempt_id,
        "--owner",
        owner,
    )


def handoff_payload(
    state: dict[str, Any],
    action: dict[str, Any],
    claim_message: str,
    *,
    owner: str | None = None,
) -> dict[str, str]:
    role = role_for_delivery(action)
    stable_owner = owner or owner_for_delivery(state, action)
    cwd = str(_main_root(state))
    prompt = (
        f"Role: {role}\n"
        f"Owner: {stable_owner}\n"
        f"CWD: {cwd}\n"
        "Claim message (verbatim):\n"
        f"{claim_message}"
    )
    return {
        "role": role,
        "owner": stable_owner,
        "cwd": cwd,
        "claim_message": claim_message,
        "prompt": prompt,
    }


def hydrate_action(
    state: dict[str, Any], action: dict[str, Any]
) -> dict[str, Any]:
    hydrated = dict(action)
    kind = str(action.get("kind") or "")
    if kind == "main-owned-action":
        hydrated["invocation"] = invocation_for_main_action(state, action)
        return hydrated
    if kind in DELIVERY_ACTION_KINDS:
        owner = owner_for_delivery(state, action)
        hydrated.update(
            {
                "role": role_for_delivery(action),
                "owner": owner,
                "cwd": str(_main_root(state)),
                "claim_invocation": claim_invocation(state, action),
            }
        )
        return hydrated
    return hydrated


def hydrate_actions(
    state: dict[str, Any], actions: Iterable[dict[str, Any]]
) -> list[dict[str, Any]]:
    return [hydrate_action(state, action) for action in actions]


def _delivery_action_for_attempt(
    state: dict[str, Any], attempt_id: str
) -> dict[str, Any] | None:
    if ":" not in attempt_id:
        attempt = state.get("attempts", {}).get(attempt_id)
        if not isinstance(attempt, dict):
            return None
        delivery = attempt.get("delivery")
        if not isinstance(delivery, dict):
            return None
        return {
            "id": str(delivery.get("action_id") or ""),
            "kind": str(delivery.get("kind") or ""),
            "phase": str(attempt.get("phase") or ""),
            "attempt_id": attempt_id,
        }
    round_id, group_id = attempt_id.split(":", 1)
    attempt = state.get("attempts", {}).get(round_id)
    group = (
        attempt.get("groups", {}).get(group_id)
        if isinstance(attempt, dict)
        else None
    )
    if not isinstance(group, dict):
        return None
    delivery = group.get("delivery")
    if not isinstance(delivery, dict):
        return None
    return {
        "id": str(delivery.get("action_id") or ""),
        "kind": str(delivery.get("kind") or ""),
        "phase": "vc-proving-preparing",
        "attempt_id": attempt_id,
        "round": round_id,
        "group_id": group_id,
    }


def hydrate_waiting_delivery(
    state: dict[str, Any], delivery: dict[str, Any]
) -> dict[str, Any]:
    hydrated = dict(delivery)
    attempt_id = str(
        delivery.get("attempt_id") or delivery.get("attempt") or ""
    )
    owner = str(delivery.get("owner") or "")
    if not attempt_id or not owner:
        return hydrated
    action = _delivery_action_for_attempt(state, attempt_id)
    if action is None or action.get("kind") not in DELIVERY_ACTION_KINDS:
        return hydrated
    hydrated.update(
        {
            "attempt": attempt_id,
            "role": role_for_delivery(action),
            "cwd": str(_main_root(state)),
            "finalize_invocation": finalize_invocation(
                state, attempt_id, owner
            ),
        }
    )
    return hydrated


def hydrate_waiting_deliveries(
    state: dict[str, Any], deliveries: Iterable[dict[str, Any]]
) -> list[dict[str, Any]]:
    return [hydrate_waiting_delivery(state, item) for item in deliveries]
