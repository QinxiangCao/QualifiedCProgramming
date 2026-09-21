"""Render controller commands and owner handoffs from current task facts."""
from __future__ import annotations

import sys
from pathlib import Path

DELIVERY_ACTION_KINDS = frozenset({
    "spawn-attempt", "append-attempt", "spawn-annotation-agent", "append-annotation-agent",
    "spawn-group-worker", "append-group-worker",
})


def invocation(state: dict, command: str, *arguments: str) -> dict:
    return {
        "argv": [sys.executable, str(Path(__file__).with_name("controller.py").resolve()),
                 "--main-root", state["main_root"], command, "--run", state["run_id"], *map(str, arguments)],
        "cwd": state["main_root"],
    }


def main_action(state: dict, command: str, **values) -> dict:
    arguments = []
    for field, option in (("round", "--round"), ("phase", "--phase"), ("reason", "--reason"),
                          ("previous_attempt", "--previous-attempt"), ("attempt_id", "--attempt"), ("owner", "--owner")):
        if field in values:
            arguments.extend([option, str(values[field])])
    identity = values.get("round", values.get("attempt_id", values.get("previous_attempt", "")))
    return {"id": f"{command}:{identity}", "kind": "main-owned-action", "action": command,
            **values, "invocation": invocation(state, command, *arguments)}


def finalize_invocation(state: dict, attempt_id: str, owner: str) -> dict:
    return invocation(state, "finalize-delivery", "--attempt", attempt_id, "--owner", owner)


def delivery_action(state: dict, attempt: dict, paths: dict, group_id: str | None = None) -> dict:
    task = attempt if group_id is None else attempt["groups"][group_id]
    identifier = attempt["attempt_id"] + (f":{group_id}" if group_id is not None else "")
    if group_id is not None:
        role, kind, default_owner = "group-worker", "group-worker", f"group-worker/{identifier}"
    elif attempt["phase"] == "annotation":
        role, kind, default_owner = "annotation-subagent", "annotation-agent", f"annotation/{state['run_id']}"
    else:
        role, kind, default_owner = "vc-checking-subagent", "attempt", f"vc-checking/{identifier}"
    owner = task.get("owner") or (state.get("annotation_owner") if kind == "annotation-agent" else None) or default_owner
    continued = bool(task.get("owner") or (kind == "annotation-agent" and state.get("annotation_owner")))
    action_id = f"deliver:{identifier}:{task.get('repair_index', 0)}"
    return {
        "id": action_id, "kind": f"{'append' if continued else 'spawn'}-{kind}",
        "attempt_id": identifier, "phase": attempt["phase"], "round": attempt["attempt_id"],
        **({"group_id": group_id} if group_id is not None else {}),
        "owner": owner, "role": role, "cwd": state["main_root"],
        "input": str(paths["input"]), "report": str(paths["report"]),
        "claim_invocation": invocation(state, "claim-attempt", "--next-action", action_id, "--owner", owner),
    }


def handoff_payload(state: dict, action: dict, claim_message: str | None = None, *, owner: str | None = None) -> dict:
    owner = owner or action["owner"]
    message = claim_message or (
        f"Read {action['input']} completely. Work only on this task and write {action['report']} last. "
        "Stop writing and notify main; main runs finalize-delivery."
    )
    return {"role": action["role"], "owner": owner, "cwd": state["main_root"], "claim_message": message,
            "prompt": f"Role: {action['role']}\nOwner: {owner}\nCWD: {state['main_root']}\n{message}"}
