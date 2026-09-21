"""One owner lifecycle for annotation, VC analysis, and proof groups.

The controller stores task facts. Actions and paths come from the current task
identity; owner reports are read once at each delivery, not copied into seals.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from controller_artifacts import _report_errors
from controller_invocations import delivery_action, finalize_invocation, handoff_payload
from controller_rounds import derive_actions, new_attempt, render_handoff, waiting
from controller_state import (
    _append_event, _current_files_errors, _elapsed_between, _failed_vcs_errors,
    _json_load, _load_state, _manual_obligations, _record_elapsed_stage, _save_state,
    _utc, attempt_paths, current_attempt, load_run, require_attempt,
)
from coq_tooling import run_coqc_check
from group_plan_utils import group_check_names
from path_utils import (
    coq_identifier_slug, fixed_path_under, group_build_workspace,
    group_debug_script_name,
)
from proof_manual_utils import manual_vc_index
from proving import validate_group
from process_adapter import ProcessCancelled

ANNOTATION_GAPS = {"annotation-gap", "specification-gap", "dependency-gap"}
VC_BLOCKERS = ANNOTATION_GAPS | {"plan-defect", "report-defect", "infrastructure"}
DELIVERY_KINDS = {
    "spawn-attempt", "append-attempt", "spawn-annotation-agent", "append-annotation-agent",
    "spawn-group-worker", "append-group-worker",
}
READ_ERRORS = (OSError, UnicodeError, ValueError, TypeError, SystemExit)


def _context(state: dict, attempt: dict):
    from controller_proving import _context as proving_context

    return proving_context(state, attempt)


def _task(state: dict, identifier: str, *, assignment: bool = True) -> tuple[dict, dict, dict | None]:
    """Resolve one current owner record and its optional proof assignment."""
    round_id, separator, group_id = identifier.partition(":")
    attempt = require_attempt(state, round_id)
    if not separator:
        if attempt["phase"] == "vc-proving":
            raise SystemExit("proving rounds are main-owned; name a round:group delivery")
        return attempt, attempt, None
    if attempt["phase"] != "vc-proving" or not group_id:
        raise SystemExit(f"invalid group delivery: {identifier}")
    record = attempt.get("groups", {}).get(group_id)
    if not isinstance(record, dict):
        raise SystemExit(f"unknown group delivery: {identifier}")
    if not assignment:
        return attempt, record, {"id": group_id}
    group = next((item for item in _context(state, attempt).groups if item["id"] == group_id), None)
    if group is None:
        raise SystemExit(f"group is absent from the current plan: {identifier}")
    return attempt, record, group


def _paths(state: dict, attempt: dict, group: dict | None) -> dict[str, Path]:
    if group is None:
        return attempt_paths(state, attempt)
    directory = fixed_path_under(Path(group["report_directory"]), Path(state["report_root"]), label="group report directory")
    return {"directory": directory, **{
        role: fixed_path_under(directory / name, directory, label=f"group {role}")
        for role, name in (("input", "group_worker_input.md"),
                           ("report", "group_worker_report.json"),
                           ("output", "group_worker_output.md"))
    }}


def _response(state: dict, status: str, **details: Any) -> int:
    print(json.dumps({
        "status": status, "phase": state["phase"], **details,
        "next_actions": derive_actions(state), "waiting_for": waiting(state),
        **({"current_blockers": state["current_blockers"]} if state["current_blockers"] else {}),
    }, indent=2, ensure_ascii=True))
    return 1 if status in {"failed", "report-repair-required"} else 0


def _save(state: dict, event: str, **details: Any) -> None:
    run_root = Path(state["run_root"])
    _save_state(run_root, state)
    _append_event(run_root, state, event, **details)


def _report(path: Path, phase: str) -> tuple[dict, list[str]]:
    try:
        payload = _json_load(path)
    except READ_ERRORS as exc:
        return {}, [f"owner report cannot be read: {exc}"]
    if not isinstance(payload, dict):
        return {}, ["owner report must be a JSON object"]
    errors = _report_errors(payload, context=phase)
    if not errors and payload["status"] == "blocked" and phase == "vc-checking":
        if payload["blocker"]["failure_class"] not in VC_BLOCKERS:
            errors.append("VC blocker must name an annotation gap, plan/report defect, or infrastructure failure")
    return payload, errors


def _vc_errors(blocker: dict, index: dict, assigned: set[str] | None = None) -> list[str]:
    if not blocker["vcs"]:
        return ["annotation/specification/dependency blocker requires actual VCs"]
    errors, seen = [], set()
    for item in blocker["vcs"]:
        name = item["name"]
        vc = index["by_name"].get(name)
        if name in seen:
            errors.append(f"blocker repeats VC: {name}")
        seen.add(name)
        if vc is None:
            errors.append(f"blocker names a VC absent from the current manual: {name}")
        elif item["parent"] != vc["parent"]:
            errors.append(f"blocker parent differs from the current manual: {name}")
        elif assigned is not None and str(vc["parent"] or name) not in assigned:
            errors.append(f"blocker names an unassigned VC: {name}")
    return errors


def _delivery_action(state: dict, attempt: dict, record: dict, group: dict | None) -> dict:
    action = delivery_action(state, attempt, _paths(state, attempt, group), group["id"] if group else None)
    action["id"] = record["claimed_action"]
    return action


def _claim_response(state: dict, attempt: dict, record: dict, group: dict | None, action: dict, status: str) -> int:
    group_id = group["id"] if group else None
    render_handoff(state, attempt, group_id=group_id, feedback=record.get("feedback"))
    paths = _paths(state, attempt, group)
    message = (f"Read {paths['input']} completely and follow its role skill and current assignment. "
               f"Write the terminal report to {paths['report']} and stop writing before main finalizes.")
    identifier = attempt["attempt_id"] + (":" + group_id if group_id else "")
    print(json.dumps({
        "status": status, "attempt": identifier, "owner": record["owner"],
        "handoff": handoff_payload(state, action, message, owner=record["owner"]),
        "finalize_invocation": finalize_invocation(state, identifier, record["owner"]),
    }, indent=2))
    return 0


def claim_attempt(args: argparse.Namespace) -> int:
    state = load_run(args)
    owner = str(args.owner).strip()
    if not owner:
        raise SystemExit("--owner must name the controller-selected owner")
    action = next((item for item in derive_actions(state) if item["id"] == args.next_action), None)
    if action is None:
        # Reissuing a claim after a lost response cannot start a second delivery.
        for identifier in state["current"].values():
            if not identifier:
                continue
            attempt = state["attempts"][identifier]
            candidates = [(attempt, None)] if attempt["phase"] != "vc-proving" else [
                (record, group_id) for group_id, record in attempt.get("groups", {}).items()
            ]
            for record, group_id in candidates:
                if record.get("claimed_action") != args.next_action or record["status"] != "running":
                    continue
                if record.get("owner") != owner:
                    raise SystemExit("delivery was claimed by another owner")
                attempt, record, group = _task(state, identifier + (":" + group_id if group_id else ""))
                return _claim_response(state, attempt, record, group,
                                       _delivery_action(state, attempt, record, group), "already-claimed")
        raise SystemExit("delivery action is not current")
    if action.get("kind") not in DELIVERY_KINDS:
        raise SystemExit("action is not an owner delivery")
    attempt, record, group = _task(state, action["attempt_id"])
    if record["status"] != "prepared":
        raise SystemExit("owner delivery is not prepared")
    expected_owner = record.get("owner") or action.get("owner")
    if expected_owner and expected_owner != owner:
        raise SystemExit("delivery is bound to another owner")
    if attempt["phase"] == "annotation":
        if state["annotation_owner"] not in {None, owner}:
            raise SystemExit("the annotation owner cannot change during a run")
        state["annotation_owner"] = owner
    record.update(status="running", owner=owner, claimed_action=action["id"], started_at=_utc())
    record.pop("returned_at", None)
    record.pop("finished_at", None)
    _save(state, "owner-claimed", attempt=action["attempt_id"], owner=owner)
    return _claim_response(state, attempt, record, group, action, "claimed")


def _close_work(record: dict) -> None:
    if record.get("started_at") and not record.get("returned_at"):
        finished = _utc()
        _record_elapsed_stage(record, "owner-work", _elapsed_between(record["started_at"], finished))
        record["returned_at"] = finished
        record.pop("started_at")


def _repair(state: dict, attempt: dict, record: dict, group: dict | None, errors: list[str]) -> int:
    record.update(status="prepared", repair_index=record.get("repair_index", 0) + 1,
                  feedback="\n".join(errors), claimed_action=None)
    for field in ("started_at", "returned_at", "finished_at", "blocker"):
        record.pop(field, None)
    render_handoff(state, attempt, group_id=group["id"] if group else None, feedback=record["feedback"])
    _save(state, "owner-repair-required", attempt=attempt["attempt_id"],
          group=group["id"] if group else None, errors=errors)
    return _response(state, "report-repair-required", errors=errors)


def _queue_retry(state: dict, phase: str, reason: str, previous: str) -> None:
    state["pending_retry"] = {"phase": phase, "reason": reason, "previous_attempt": previous}


def _blocked(state: dict, attempt: dict, record: dict, group: dict | None, blocker: dict) -> int:
    record.update(status="blocked", blocker=blocker, finished_at=_utc())
    identifier = attempt["attempt_id"] + (":" + group["id"] if group else "")
    failure = blocker["failure_class"]
    if failure == "current-file-drift":
        _queue_retry(state, "annotation", "current-file-drift", identifier)
        state["current_blockers"] = [blocker]
    elif group is None and attempt["phase"] == "vc-checking" and failure in ANNOTATION_GAPS:
        _queue_retry(state, "annotation", "vc-checking-annotation-gap", identifier)
        state["current_blockers"] = [blocker]
    elif group is None and attempt["phase"] == "vc-checking" and failure in {"plan-defect", "report-defect"}:
        _queue_retry(state, "vc-checking", "vc-checking-plan-defect", identifier)
        state["current_blockers"] = [blocker]
    elif group is None or failure not in {"annotation-gap", "plan-defect"}:
        state["current_blockers"] = [blocker]
    # Group annotation gaps and plan defects wait for the scheduler's batch rule.
    _save(state, "owner-blocked", attempt=identifier, blocker=blocker)
    return _response(state, "blocked", blocker=blocker)


def group_tooling(state: dict, attempt: dict, group: dict) -> dict:
    target = state["target_files"]
    run_root = Path(state["run_root"])
    directory = Path(group["directory"])
    workspace = fixed_path_under(group_build_workspace(run_root, attempt["attempt_id"], directory.name), run_root,
                                 label="group build workspace")
    name = coq_identifier_slug(directory.name)
    overlays = {Path(target["proof_manual_file"]): Path(group["proof_manual"])}
    if group.get("group_worker_lib"):
        overlays[Path(target["formal_case_lib"])] = Path(group["group_worker_lib"])
    return {
        "build_workspace": workspace, "development_build_workspace": workspace.parent / "dev",
        "target_file": Path(target["formal_directory"]) / f"{state['case']}_{name}_check.v",
        "debug_script": Path(".coq_debug") / group_debug_script_name(directory.name),
        "overlays": overlays,
        "group_check": {"case_theory": target["active_case_theory"],
                        "require_modules": [state["case"] + suffix for suffix in ("_goal", "_proof_auto", "_proof_manual")],
                        "assigned_witnesses": group_check_names(group)},
    }


def execute_group_check(state: dict, attempt: dict, group: dict | str, *, context, development: bool = False) -> dict:
    """Use the same current-group validation for owner feedback and acceptance."""
    group_id = group if isinstance(group, str) else group["id"]
    validation = validate_group(context, group_id, complete=not development)
    if validation["errors"]:
        return {"status": "failed", "returncode": 2, "errors": validation["errors"],
                "recoverable": validation["recoverable"],
                "first_failure": {"category": "structure", "kind": "group-structure",
                                  "message": validation["errors"][0]}}
    group = validation["group"]
    tooling = group_tooling(state, attempt, group)
    result = run_coqc_check(
        workspace_root=Path(state["main_root"]),
        build_workspace=tooling["development_build_workspace"] if development else tooling["build_workspace"],
        target_file=Path(state["target_files"]["proof_manual_file"]) if development else tooling["target_file"],
        target_kind="group-development" if development else "group-check",
        group_check=None if development else tooling["group_check"], overlays=tooling["overlays"],
        incremental=development, current_case_anchor=Path(state["target_files"]["proof_auto_file"]),
    )
    result["recoverable"] = True
    return result


def _blocked_report_errors(state: dict, attempt: dict, group: dict | None, blocker: dict, context) -> list[str]:
    if group is None:
        if attempt["phase"] == "vc-checking" and blocker["failure_class"] in ANNOTATION_GAPS:
            return _vc_errors(blocker, _manual_obligations(state))
        return []
    if blocker["failure_class"] != "annotation-gap":
        if blocker["failure_class"] in {"specification-gap", "dependency-gap", "current-file-drift"}:
            return ["group semantic gaps must use annotation-gap; file drift is detected by the controller"]
        return []
    text = Path(group["proof_manual"]).read_text(encoding="utf-8")
    errors = _vc_errors(blocker, manual_vc_index(text), {item["name"] for item in group["witnesses"]})
    output = _paths(state, attempt, group)["output"]
    if not output.is_file() or not output.read_text(encoding="utf-8").strip():
        errors.append("annotation-gap requires non-empty group_worker_output.md")
    if not errors:
        errors.extend(validate_group(context, group["id"], complete=False)["errors"])
    return errors


def _result_errors(result: dict) -> list[str]:
    if result.get("errors"):
        return [str(item) for item in result["errors"]]
    failure = result.get("first_failure")
    if isinstance(failure, dict) and failure.get("message"):
        return [str(failure["message"])]
    return [str(result.get("message") or result.get("stderr_tail") or "controller acceptance check failed")]


def finalize_delivery(args: argparse.Namespace) -> int:
    """Record that the owner stopped, then accept or repair this exact delivery."""
    state = load_run(args)
    attempt, record, group = _task(state, str(args.attempt), assignment=False)
    if not record.get("owner") or record["owner"] != str(args.owner).strip():
        raise SystemExit("delivery was not claimed by this owner")
    if record["status"] in {"accepted", "blocked", "prepared"}:
        return _response(state, "already-finalized", attempt=args.attempt)
    if record["status"] == "running":
        _close_work(record)
        record["status"] = "returned"
        _save(state, "owner-returned", attempt=args.attempt, owner=record["owner"])
    if record["status"] != "returned":
        raise SystemExit("delivery must be claimed before finalization")

    if attempt["phase"] != "annotation":
        errors = _current_files_errors(state)
        if errors:
            return _blocked(state, attempt, record, group, {
                "failure_class": "current-file-drift", "kind": "current-inputs", "vcs": [],
                "message": errors[0], "repair_boundary": "annotation",
            })
    try:
        context = _context(state, attempt) if group else None
        if group:
            group = next(item for item in context.groups if item["id"] == group["id"])
        report, errors = _report(_paths(state, attempt, group)["report"], attempt["phase"])
        if not errors and report["status"] == "blocked":
            errors = _blocked_report_errors(state, attempt, group, report["blocker"], context)
        if errors:
            return _repair(state, attempt, record, group, errors)
        if report["status"] == "blocked":
            blocker = report["blocker"]
            if group is None and attempt["phase"] == "annotation" and blocker["failure_class"] in ANNOTATION_GAPS:
                return _repair(state, attempt, record, group, [blocker["message"]])
            return _blocked(state, attempt, record, group, blocker)
        if group is not None:
            result = execute_group_check(state, attempt, group, context=context)
        else:
            from controller_round_checks import annotation_accept, vc_accept

            result = (annotation_accept if attempt["phase"] == "annotation" else vc_accept)(state, attempt)
    except ProcessCancelled:
        raise
    except READ_ERRORS as exc:
        return _repair(state, attempt, record, group, [str(exc)])

    # A pause or another state transition during a native check cannot be lost.
    current = _load_state(Path(state["run_root"]))
    fresh_attempt, fresh_record, fresh_group = _task(current, str(args.attempt), assignment=False)
    if fresh_record["status"] != "returned" or fresh_record.get("owner") != record["owner"]:
        raise SystemExit("owner delivery changed while acceptance was running")
    if current["run_control"]["status"] == "paused":
        return _response(current, "paused")
    # The annotation checker may update the authorized specification baseline.
    if attempt["phase"] == "annotation" and result.get("status") == "passed":
        current["spec_freeze"] = state["spec_freeze"]
    state, attempt, record, group = current, fresh_attempt, fresh_record, fresh_group
    if result.get("status") != "passed":
        errors = _result_errors(result)
        if result.get("recoverable") is False:
            return _blocked(state, attempt, record, group, {
                "failure_class": "infrastructure", "kind": "acceptance-input", "vcs": [],
                "message": errors[0], "repair_boundary": "controller inputs",
            })
        return _repair(state, attempt, record, group, errors)
    record.update(status="accepted", finished_at=_utc())
    record.pop("feedback", None)
    record.pop("blocker", None)
    if group is None and attempt["phase"] == "annotation":
        state["dune_preparation"] = None
        state["phase"] = "dependencies"
    elif group is None:
        new_attempt(state, "vc-proving")
    _save(state, "owner-accepted", attempt=args.attempt)
    return _response(state, "accepted", attempt=args.attempt)


def _feedback(state: dict, identifier: str) -> tuple[dict, dict, Path | None]:
    """Read a historical source using paths derived from its original round."""
    round_id, _, group_id = identifier.partition(":")
    attempt = state["attempts"].get(round_id)
    if not isinstance(attempt, dict):
        raise ValueError(f"feedback round is missing: {round_id}")
    if group_id:
        group = next((item for item in _context(state, attempt).groups if item["id"] == group_id), None)
        if group is None:
            raise ValueError(f"feedback group is missing: {identifier}")
        paths = _paths(state, attempt, group)
        manual = Path(group["proof_manual"])
        role = "group"
    else:
        paths = attempt_paths(state, attempt)
        annotation_id = (attempt["attempt_id"] if attempt["phase"] == "annotation"
                         else attempt.get("source_annotation"))
        annotation = state["attempts"].get(annotation_id)
        manual = (attempt_paths(state, annotation)["after"] / state["target_files"]["proof_manual_file"]
                  if annotation else None)
        role = attempt["phase"]
    report, errors = _report(paths["report"], role)
    if errors:
        raise ValueError(errors[0])
    source = {"phase": role, "attempt_id": identifier,
              "evidence": [str(paths[key]) for key in ("report", "output") if paths[key].is_file()]}
    return source, report, manual


def _retry_sources(state: dict, previous: str) -> tuple[list[dict], list[dict]]:
    """Collect exact current blockers; models read the provided history themselves."""
    attempt = state["attempts"].get(previous)
    if attempt and attempt["phase"] == "vc-proving":
        identifiers = [f"{previous}:{group['id']}" for group in _context(state, attempt).groups
                       if attempt["groups"][group["id"]]["status"] == "blocked"]
    else:
        identifiers = [previous]
    sources, failed_vcs = [], []
    for identifier in identifiers:
        source, report, manual = _feedback(state, identifier)
        sources.append(source)
        blocker = report.get("blocker")
        if not isinstance(blocker, dict) or blocker["failure_class"] not in ANNOTATION_GAPS:
            continue
        if manual is None:
            raise ValueError(f"annotation gap has no historical manual: {identifier}")
        manual = fixed_path_under(manual, Path(state["run_root"]), label="failed VC manual")
        errors = _vc_errors(blocker, manual_vc_index(manual.read_text(encoding="utf-8")))
        if errors:
            raise ValueError(errors[0])
        failed_vcs.extend({"source_attempt": identifier, "manual": str(manual),
                           "message": blocker["message"], **vc} for vc in blocker["vcs"])
    errors = _failed_vcs_errors(failed_vcs, run_root=Path(state["run_root"]))
    if errors:
        raise ValueError(errors[0])
    return sources, failed_vcs


def _unfinished_deliveries(state: dict) -> bool:
    for identifier in state["current"].values():
        if not identifier:
            continue
        attempt = state["attempts"][identifier]
        records = attempt.get("groups", {}).values() if attempt["phase"] == "vc-proving" else [attempt]
        if any(record["status"] in {"running", "returned"} for record in records):
            return True
    return False


def retry_round(args: argparse.Namespace) -> int:
    state = load_run(args)
    requested = {"phase": args.phase, "reason": args.reason, "previous_attempt": args.previous_attempt}
    authorized = any(action.get("action") == "retry-round"
                     and all(action.get(key) == value for key, value in requested.items())
                     for action in derive_actions(state))
    if not authorized:
        current = current_attempt(state, args.phase)
        if current and current.get("retry_reason") == args.reason and current.get("retry_previous_attempt") == args.previous_attempt:
            return _response(state, "already-retried", attempt=current["attempt_id"])
        raise SystemExit("retry-round does not match the current controller decision")
    if _unfinished_deliveries(state):
        raise SystemExit("finish all running or returned owners before retrying a round")
    if (state.get("final_apply") or {}).get("status") in {"applied", "rollback-failed"}:
        raise SystemExit("a published candidate must be checked or rolled back before retry")
    try:
        sources, failed_vcs = _retry_sources(state, args.previous_attempt)
    except READ_ERRORS as exc:
        # Mechanical recovery can start from unreadable current artifacts. Its
        # recorded controller blocker is the evidence, not an invented VC gap.
        if not state["current_blockers"] or any(item.get("failure_class") in ANNOTATION_GAPS for item in state["current_blockers"]):
            raise SystemExit(str(exc)) from exc
        sources, failed_vcs = [], []
    if args.phase == "annotation" and not failed_vcs and not state["current_blockers"]:
        raise SystemExit("annotation retry requires an actual VC gap or controller failure")
    if args.phase == "annotation":
        state["current"]["vc-checking"] = None
        state["dune_preparation"] = None
    state["current"]["vc-proving"] = None
    state["final_candidate"] = state["final_apply"] = state["final_check"] = None
    feedback = list(state["current_blockers"])
    state["pending_retry"] = None
    state["current_blockers"] = []
    attempt = new_attempt(state, args.phase, failed_vcs=failed_vcs if args.phase == "annotation" else None,
                          feedback_sources=sources, reason=args.reason, previous_attempt=args.previous_attempt)
    attempt["retry_reason"] = args.reason
    attempt["retry_previous_attempt"] = args.previous_attempt
    if feedback:
        attempt["feedback"] = json.dumps(feedback, ensure_ascii=False, indent=2)
    render_handoff(state, attempt, feedback=attempt.get("feedback"))
    _save(state, "round-retried", attempt=attempt["attempt_id"], previous=args.previous_attempt, phase=args.phase)
    return _response(state, "prepared", attempt=attempt["attempt_id"])
