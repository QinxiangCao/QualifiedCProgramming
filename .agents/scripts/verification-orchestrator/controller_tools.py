"""Run owner tools against the current task; generation publishes only complete output."""
from __future__ import annotations

import json
import tempfile
from pathlib import Path

from annotation_refresh import (
    AnnotationRefreshError, file_contents, generated_output_contents, publish_generated_output,
    recover_interrupted_refresh, transaction_root_for_attempt,
)
from controller_control import control_signal_path
from controller_execution import start_group_tool_log
from controller_state import (
    _formal_case_lib_is_active, _formal_case_lib_snapshot, _generated_artifact_module_spellings_for_state,
    _load_state, attempt_paths, load_run, require_attempt,
)
from coq_tooling import run_coqc_check, run_coqtop_debug
from file_integrity import _lexical_regular_file_snapshot, _snapshot_text
from path_utils import fixed_path_under
from process_adapter import control_signal_requests_stop
from proof_manual_utils import lib_contract_errors
from symexec_tooling import run_symexec, symexec_profile_for_state


def failed(message: str, kind: str = "current-input", category: str = "contract") -> dict:
    return {"status": "failed", "returncode": 2,
            "first_failure": {"category": category, "kind": kind, "message": message}}


def _running(state: dict, identifier: str, phase: str) -> dict:
    task = require_attempt(state, identifier, phase)
    if state["phase"] != phase or task["status"] != "running" or not task.get("owner"):
        raise SystemExit("tool requires a currently claimed, running owner")
    return task


def refresh_annotation(state: dict, task: dict, *, progress_name="symexec-progress.json") -> dict:
    """One generation and one publication; both owner feedback and acceptance use it."""
    root, run = Path(state["main_root"]), Path(state["run_root"])
    target = state["target_files"]
    report = attempt_paths(state, task)["directory"]
    try:
        recover_interrupted_refresh(main_root=root, target_files=target,
                                    transaction_root=transaction_root_for_attempt(report))
        expected = generated_output_contents(root, target)
        sources = {key: target[key] for key in ("c_file", "formal_case_lib")}
        before = file_contents(root, sources)
        with tempfile.TemporaryDirectory(prefix=".gen-", dir=report, ignore_cleanup_errors=True) as temporary:
            profile = symexec_profile_for_state(state)
            result = run_symexec(
                main_root=root, target_c_file=Path(target["c_file"]), target_files=target, output_root=Path(temporary),
                timeout_seconds=profile["timeout_seconds"], profile_name=profile["name"],
                heartbeat_seconds=profile["heartbeat_seconds"], poll_interval_seconds=profile["poll_interval_seconds"],
                progress_path=report / progress_name,
                cancel_requested=lambda: control_signal_requests_stop(control_signal_path(state)),
            )
            if result["status"] != "passed":
                return result
            current = _load_state(run)
            current_task = require_attempt(current, task["attempt_id"], "annotation")
            if (current["generation"] != state["generation"] or current_task["status"] != task["status"]
                    or current_task.get("owner") != task.get("owner")
                    or control_signal_requests_stop(control_signal_path(current))):
                return failed("annotation owner or run control changed during generation", "generation-authority")
            if file_contents(root, sources) != before:
                return failed("annotation sources changed during generation", "generation-inputs")
            result["publication"] = publish_generated_output(
                main_root=root, target_files=target, output_root=Path(temporary), report_directory=report, expected=expected)
            return result
    except AnnotationRefreshError as exc:
        return {"status": "failed", "returncode": 2, "first_failure": exc.failure()}
    except (OSError, ValueError) as exc:
        return failed(str(exc), "generation-inputs")


def library_check(state: dict, task: dict, *, design: bool = False) -> dict:
    target = state["target_files"]
    snapshot = _formal_case_lib_snapshot(state)
    if not _formal_case_lib_is_active(state):
        return {"status": "passed", "skipped": True} if snapshot["state"] == "missing" else failed("absent case library must remain absent")
    try:
        text = _snapshot_text(snapshot, label="case library")
        errors = lib_contract_errors(text, forbidden_modules=_generated_artifact_module_spellings_for_state(state))
        if errors:
            return failed(errors[0], "case-library-contract")
    except ValueError as exc:
        return failed(str(exc), "case-library-contract")
    relative = Path(target["formal_case_lib"])
    result = run_coqc_check(
        workspace_root=Path(state["main_root"]),
        build_workspace=Path(state["run_root"]) / "_coq_builds" / task["attempt_id"] / "library" / "src",
        target_file=relative, target_kind="formal-case-lib-design" if design else "formal-case-lib",
        current_case_anchor=relative if design else Path(target["proof_auto_file"]),
    )
    current = _formal_case_lib_snapshot(state)
    if current["state"] != snapshot["state"] or current.get("data") != snapshot.get("data"):
        return failed("case library changed during validation", "case-library-inputs")
    return result


def _group(state: dict, round_id: str, group_id: str):
    from controller_proving import _context
    task = require_attempt(state, round_id, "vc-proving")
    record = task.get("groups", {}).get(group_id)
    if state["phase"] != "vc-proving" or not record or record["status"] != "running" or not record.get("owner"):
        raise SystemExit("group tool requires a currently claimed, running owner")
    context = _context(state, task)
    group = next((item for item in context.groups if item["id"] == group_id), None)
    if group is None:
        raise SystemExit("group is absent from the current plan")
    return task, group, context


def _result(args, result: dict) -> int:
    if getattr(args, "group", None):
        args._tool_evidence = result
    print(json.dumps(result, indent=2, ensure_ascii=True))
    return 0 if result.get("status") == "passed" else 1


def symexec(args) -> int:
    state = load_run(args)
    return _result(args, refresh_annotation(state, _running(state, args.round, "annotation")))


def coq_check(args) -> int:
    state = load_run(args)
    if args.target_kind in {"formal-case-lib-design", "formal-case-lib"}:
        if args.group:
            raise SystemExit("library checks do not take --group")
        result = library_check(state, _running(state, args.round, "annotation"), design=args.target_kind.endswith("-design"))
    else:
        from controller_attempts import execute_group_check
        task, group, context = _group(state, args.round, args.group)
        start_group_tool_log(args, state, group, "coq-check")
        result = execute_group_check(state, task, group, context=context, development=args.target_kind == "group-development")
    return _result(args, result)


def coq_debug(args) -> int:
    state = load_run(args)
    if args.group:
        from controller_attempts import group_tooling
        from proving import validate_group
        task, group, context = _group(state, args.round, args.group)
        start_group_tool_log(args, state, group, "coq-debug")
        checked = validate_group(context, args.group, complete=False)
        if checked["errors"]:
            return _result(args, failed(checked["errors"][0], "group-structure"))
        tooling = group_tooling(state, task, group)
        build, script, overlays = tooling["build_workspace"], tooling["debug_script"], tooling["overlays"]
    else:
        from controller_round_checks import debug_manual_errors
        task = _running(state, args.round, "vc-checking")
        errors = debug_manual_errors(state, task)
        if errors:
            return _result(args, failed(errors[0], "debug-manual"))
        script = Path(state["target_files"]["proof_manual_file"])
        build = Path(state["run_root"]) / "_coq_builds" / task["attempt_id"] / "vc-checking" / "src"
        overlays = {script: attempt_paths(state, task)["debug_manual"]}
    return _result(args, run_coqtop_debug(
        workspace_root=Path(state["main_root"]), build_workspace=build, debug_script=script,
        overlays=overlays, current_case_anchor=Path(state["target_files"]["proof_auto_file"])))
