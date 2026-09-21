"""Create tasks and derive the next action from their current status."""
from __future__ import annotations

import json
from pathlib import Path

from controller_invocations import delivery_action, finalize_invocation, invocation, main_action
from controller_state import (
    _archive_annotation_stage, _formal_case_lib_is_active, _json_load, _manual_obligations,
    _save_state, _utc, attempt_paths, current_attempt, load_run,
)
from file_integrity import _lexical_regular_file_snapshot, _snapshot_text
from path_utils import fixed_path_under, write_bytes, write_json, write_text

DEFAULT_MAX_PARALLEL_GROUP_WORKERS = 5
VC_CHECKING_BLOCKER_RETRY_PHASES = {
    "annotation-gap": "annotation", "specification-gap": "annotation", "dependency-gap": "annotation",
    "plan-defect": "vc-checking", "report-defect": "vc-checking",
}


def annotation_plan() -> dict:
    return {"version": 2, "status": "planning", "function_specs": [], "loop_invariants": [],
            "new_predicates": [], "vc_comparisons": []}


def new_attempt(state: dict, phase: str, *, failed_vcs=None, feedback_sources=None,
                reason=None, previous_attempt=None) -> dict:
    previous = [task for task in state["attempts"].values() if task["phase"] == phase]
    number = max((int(task["attempt_id"].rsplit("-r", 1)[1]) for task in previous), default=0) + 1
    identifier = f"{state['case']}-{phase}-r{number}"
    task = {"attempt_id": identifier, "phase": phase, "status": "prepared", "owner": None,
            "claimed_action": None, "repair_index": 0, "created_at": _utc()}
    if feedback_sources:
        task["feedback_sources"] = feedback_sources
    if reason:
        task["reason"] = reason
    if phase == "annotation":
        task["failed_vcs"] = failed_vcs or []
    else:
        task["source_annotation"] = state["current"]["annotation"]
        if phase == "vc-proving":
            task.update(source_vc_checking=state["current"]["vc-checking"], groups={})
    state["attempts"][identifier] = task
    state["current"][phase] = identifier
    state["phase"] = phase
    state["pending_retry"] = None
    state["current_blockers"] = []
    paths = attempt_paths(state, task)
    paths["directory"].mkdir(parents=True, exist_ok=True)
    if phase == "annotation":
        plan = annotation_plan()
        if previous:
            old = _json_load(attempt_paths(state, previous[-1])["plan"], {})
            for key in ("function_specs", "loop_invariants", "new_predicates"):
                plan[key] = old.get(key, [])
        write_json(paths["plan"], plan)
        _archive_annotation_stage(state, task, "before")
    elif phase == "vc-checking":
        relative = state["target_files"]["proof_manual_file"]
        snapshot = _lexical_regular_file_snapshot(root=Path(state["main_root"]), relative=relative, label="VC manual")
        _snapshot_text(snapshot, label="VC manual")
        write_bytes(paths["debug_manual"], snapshot["data"])
    if phase != "vc-proving":
        write_json(paths["report"], {"status": "pending"})
        render_handoff(state, task)
    return task


def group_paths(group: dict) -> dict[str, Path]:
    root = Path(group["report_directory"])
    return {"directory": root, "input": root / "group_worker_input.md",
            "report": root / "group_worker_report.json", "output": root / "group_worker_output.md"}


def previous_proving_round(state: dict, task: dict) -> str | None:
    previous = None
    for identifier, candidate in state["attempts"].items():
        if identifier == task["attempt_id"]:
            break
        if candidate["phase"] == "vc-proving":
            previous = identifier
    return previous


def render_handoff(state: dict, task: dict, group_id: str | None = None, feedback=None) -> None:
    if feedback is not None:
        (task if group_id is None else task["groups"][group_id])["feedback"] = feedback
    if group_id is not None:
        from controller_proving import _context
        from path_utils import render_group_worker_input
        ctx = _context(state, task)
        group = next(item for item in ctx.groups if item["id"] == group_id)
        paths = group_paths(group)
        write_text(paths["input"], render_group_worker_input(
            group=group, commands=group["commands"],
            formal_case_lib=ctx.formal_case_lib.as_posix() if ctx.library is not None else None,
            report_dir=paths["directory"],
            repair_index=task["groups"][group_id].get("repair_index", 0),
            repair_feedback=task["groups"][group_id].get("feedback"),
        ))
        return
    paths = attempt_paths(state, task)
    phase = task["phase"]
    skill = "annotation-designing" if phase == "annotation" else "vc-checking"
    target = state["target_files"]
    assignment = {"attempt": task["attempt_id"], "round": task["attempt_id"],
                  "main_root": state["main_root"], "target_files": target,
                  "formal_case_lib_policy": state["formal_case_lib_policy"],
                  "report": str(paths["report"]), "notes": str(paths["output"]),
                  "feedback": task.get("feedback"), "feedback_sources": task.get("feedback_sources", []),
                  "previous_attempt": task.get("retry_previous_attempt")}
    if phase == "annotation":
        assignment.update(plan=str(paths["plan"]), problem=state["problem_context"],
                          failed_vcs=task.get("failed_vcs", []), feedback_sources=task.get("feedback_sources", []),
                          writable_files=[target["c_file"]] + ([target["formal_case_lib"]] if _formal_case_lib_is_active(state) else []))
        freeze = state.get("spec_freeze")
        assignment["user_spec"] = {"functions": freeze["functions"], "frozen": freeze["baseline"] is not None} if freeze else None
        commands = [invocation(state, "coq-check", "--round", task["attempt_id"], "--target-kind", "formal-case-lib-design"),
                    invocation(state, "symexec", "--round", task["attempt_id"])]
        if _formal_case_lib_is_active(state):
            commands.append(invocation(state, "coq-check", "--round", task["attempt_id"], "--target-kind", "formal-case-lib"))
        rule = ("Edit only the listed annotation sources. Generated files change only through symexec. "
                "A frozen user spec needs user approval and main's unfreeze before changes. "
                "Keep correcting gaps in this attempt; every failed VC comparison must be resolved.")
    else:
        annotation = state["attempts"][task["source_annotation"]]
        plan = _json_load(attempt_paths(state, annotation)["plan"], {})
        assignment.update(group_plan=str(paths["group_plan"]), debug_manual=str(paths["debug_manual"]),
                          obligations=_manual_obligations(state), max_witnesses_per_group=state["max_witnesses_per_group"],
                          annotation_comparisons=plan.get("vc_comparisons", []))
        commands = [invocation(state, "coq-debug", "--round", task["attempt_id"])]
        rule = ("Canonical sources are read-only. Add Show only to the debug copy. "
                "Follow the structural scan and split-first workflow. Plan array order defines dispatch order.")
    skill_path = Path(__file__).resolve().parents[2] / "skills" / skill / "SKILL.md"
    write_text(paths["input"], f"# {phase}\n\nRead {skill_path} and its required documents.\n\n"
               f"{rule}\n\n```json\n{json.dumps(assignment, indent=2, ensure_ascii=True)}\n```\n\n"
               "Use exact argv and cwd. A shell-only tool must quote arguments for its actual shell. "
               "Keep the terminal session until exit; checks need exit code 0 and JSON passed.\n\n"
               f"```json\n{json.dumps(commands, indent=2)}\n```\n\n"
               "Write the terminal report last, stop writing, and notify main to finalize.\n")


def _task_action(state: dict, attempt: dict, paths: dict, group_id=None) -> list[dict]:
    task = attempt if group_id is None else attempt["groups"][group_id]
    identifier = attempt["attempt_id"] + (f":{group_id}" if group_id is not None else "")
    if task["status"] == "prepared":
        return [delivery_action(state, attempt, paths, group_id)]
    if task["status"] == "returned":
        return [main_action(state, "finalize-delivery", attempt_id=identifier, owner=task["owner"])]
    return []


def _group_actions(state: dict, attempt: dict) -> list[dict]:
    from controller_proving import _context
    ctx = _context(state, attempt)
    records = attempt["groups"]
    if set(records) != {group["id"] for group in ctx.groups}:
        raise ValueError("prepared groups no longer match the current plan")
    groups = {group["id"]: group for group in ctx.groups}
    returned = [action for identifier, record in records.items() if record["status"] == "returned"
                for action in _task_action(state, attempt, group_paths(groups[identifier]), identifier)]
    running = sum(record["status"] == "running" for record in records.values())
    gaps = [identifier for identifier, record in records.items()
            if record["status"] == "blocked" and record.get("blocker", {}).get("failure_class") == "annotation-gap"]
    terminal = [record for record in records.values() if record["status"] == "blocked" and record.get("blocker", {}).get("failure_class") != "annotation-gap"]
    annotation = state["attempts"][attempt["source_annotation"]]
    comparisons = _json_load(attempt_paths(state, annotation)["plan"], {}).get("vc_comparisons", [])
    index = _manual_obligations(state)["by_name"]
    names = {index[name]["parent"] or name for comparison in comparisons for name in comparison["current"] if name in index}
    priority = {group["id"] for group in ctx.groups if any(witness["name"] in names for witness in group["witnesses"])}
    priority_gap = any(identifier in priority for identifier in gaps)
    if priority_gap or terminal:
        if running or returned:
            return returned
        if priority_gap:
            return [main_action(state, "retry-round", phase="annotation", reason="priority-group-annotation-gaps",
                                previous_attempt=attempt["attempt_id"])]
        if all(record.get("blocker", {}).get("failure_class") == "plan-defect" for record in terminal):
            return [main_action(state, "retry-round", phase="vc-checking", reason="group-plan-defect",
                                previous_attempt=attempt["attempt_id"])]
        return []
    unfinished = [identifier for identifier, record in records.items() if record["status"] in {"prepared", "running", "returned"}]
    if not unfinished:
        if gaps:
            return [main_action(state, "retry-round", phase="annotation", reason="group-worker-annotation-gaps",
                                previous_attempt=attempt["attempt_id"])]
        return [main_action(state, "vc-proving-verify", round=attempt["attempt_id"])]
    priority_pending = any(records[identifier]["status"] != "accepted" for identifier in priority)
    slots = max(0, state["max_parallel_group_workers"] - running)
    actions = list(returned)
    for group in ctx.groups:
        identifier = group["id"]
        if slots and records[identifier]["status"] == "prepared" and (not priority_pending or identifier in priority):
            actions.extend(_task_action(state, attempt, group_paths(group), identifier))
            slots -= 1
    return actions


def derive_actions(state: dict) -> list[dict]:
    if state["run_control"]["status"] == "paused" or state["phase"] == "done":
        return []
    retry = state.get("pending_retry")
    if retry:
        returned = []
        for phase in ("annotation", "vc-checking", "vc-proving"):
            task = current_attempt(state, phase)
            if task is None:
                continue
            records = [(task["attempt_id"], task)] if phase != "vc-proving" else [
                (f"{task['attempt_id']}:{name}", record) for name, record in task.get("groups", {}).items()]
            returned.extend(main_action(state, "finalize-delivery", attempt_id=identifier, owner=record["owner"])
                            for identifier, record in records if record["status"] == "returned")
        if returned:
            return returned
        return [] if waiting(state) else [main_action(state, "retry-round", **retry)]
    phase = state["phase"]
    if phase in {"annotation", "vc-checking"}:
        task = current_attempt(state, phase)
        return _task_action(state, task, attempt_paths(state, task)) if task else []
    if phase == "dependencies":
        return [] if state["current_blockers"] else [main_action(state, "dune-build")]
    if phase == "vc-proving":
        task = current_attempt(state, phase)
        if task["status"] == "prepared":
            return [main_action(state, "vc-proving-preparing", round=task["attempt_id"])]
        if task["status"] == "running":
            return _group_actions(state, task)
        return []
    if phase in {"final-apply", "final-check"}:
        return [] if state["current_blockers"] else [main_action(state, phase)]
    return []


def waiting(state: dict) -> list[dict]:
    if state["run_control"]["status"] == "paused":
        return []
    result = []
    for phase in ("annotation", "vc-checking", "vc-proving"):
        attempt = current_attempt(state, phase)
        if not attempt:
            continue
        tasks = [(attempt["attempt_id"], attempt)] if phase != "vc-proving" else [
            (f"{attempt['attempt_id']}:{identifier}", task) for identifier, task in attempt.get("groups", {}).items()]
        for identifier, task in tasks:
            if task["status"] == "running":
                result.append({"attempt_id": identifier, "owner": task["owner"], "status": "running",
                               "finalize_invocation": finalize_invocation(state, identifier, task["owner"])})
    return result


def require_action(state: dict, command: str, **values) -> dict:
    for action in derive_actions(state):
        if action.get("action") == command and all(action.get(key) == value for key, value in values.items()):
            return action
    raise SystemExit(f"command does not match a current action: {command}")


def step(args) -> int:
    state = load_run(args)
    if state["phase"] == "intake" and state["run_control"]["status"] == "active":
        new_attempt(state, "annotation")
        _save_state(Path(state["run_root"]), state)
    try:
        actions = derive_actions(state)
        waits = waiting(state)
        blockers = list(state["current_blockers"])
        task = current_attempt(state, state["phase"])
        if task and task["status"] == "blocked" and task.get("blocker"):
            blockers.append(task["blocker"])
        if task and task["phase"] == "vc-proving":
            blockers.extend(record["blocker"] for record in task.get("groups", {}).values()
                            if record["status"] == "blocked" and record.get("blocker"))
        if not actions and not waits and not blockers and state["phase"] != "done" and state["run_control"]["status"] != "paused":
            blockers = [{"failure_class": "controller-state", "kind": "controller-no-progress",
                         "message": "Unfinished phase has no action, running owner, or reported blocker."}]
    except (ValueError, OSError, SystemExit) as exc:
        actions, waits = [], waiting(state)
        blockers = [{"failure_class": "controller-input", "message": str(exc)}]
    print(json.dumps({"phase": state["phase"], "status": state["run_control"]["status"],
                      "next_actions": actions, "waiting_for": waits, "current_blockers": blockers}, indent=2))
    return 0
