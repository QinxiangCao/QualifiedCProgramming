#!/usr/bin/env python3
"""Main-owned checks that accept annotation and vc-checking rounds.

This module is internal to controller.py.  It replays required tooling,
validates a round against current formal state, and records acceptance.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from coq_tooling import run_coqc_check
from group_plan_utils import group_entries_from_plan
from path_utils import run_builds_root, write_json
from proof_manual_utils import lib_contract_errors, manual_diagnostic_errors, write_split_manual_artifacts
from symexec_tooling import run_symexec

from controller_state import (
    _append_event,
    _current_version_errors,
    _json_load,
    _load_state,
    _run_root_from_id,
    _save_state,
    _source_goal_version,
    _source_version_for_state,
    _record_elapsed_stage,
    _utc,
)
from controller_attempts import _attempt_for_round, _queue_annotation_feedback


def _set_annotation_session_idle(state: dict[str, Any]) -> None:
    session = state.get("annotation_session")
    if isinstance(session, dict):
        session["status"] = "idle"


def annotation_check_round(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, "annotation")
    if attempt.get("status") != "ready-for-main-check":
        raise SystemExit("annotation attempt is not ready for main-owned checking")
    target = state["target_files"]
    symexec = run_symexec(main_root=main_root, target_c_file=Path(target["c_file"]), output_root=main_root)
    symexec["controller_entrypoint"] = "annotation-check-round"
    if symexec.get("elapsed_seconds") is not None:
        _record_elapsed_stage(attempt, "symexec", float(symexec["elapsed_seconds"]))
        _save_state(run_root, state)
    if symexec.get("status") != "passed":
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {"symexec": {"status": symexec.get("status"), "returncode": symexec.get("returncode")}}
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(state, attempt["attempt_id"], "annotation-main-check-symexec")
        _append_event(run_root, state, "annotation-check-failed", reason="symexec")
        _save_state(run_root, state)
        print(json.dumps({"status": "failed", "symexec": symexec}, indent=2))
        return 1
    manual = main_root / target["proof_manual_file"]
    split = write_split_manual_artifacts(
        manual,
        diagnostics_path=main_root / target["proof_diagnostics_file"],
        snapshot_path=main_root / target["diagnostics_snapshot"],
    )
    diagnostic_errors = manual_diagnostic_errors(manual.read_text(encoding="utf-8"))
    if diagnostic_errors:
        raise SystemExit("cleaned proof manual still contains diagnostics: " + "; ".join(diagnostic_errors))
    formal_case_lib = main_root / target["formal_case_lib"]
    formal_case_lib_errors = lib_contract_errors(formal_case_lib.read_text(encoding="utf-8"))
    if formal_case_lib_errors:
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
            "symexec": {"status": symexec.get("status"), "returncode": symexec.get("returncode")},
            "diagnostics_split": {key: split.get(key) for key in ("manual_obligation_count", "diagnostic_count")},
            "formal_case_lib_contract": {"status": "failed", "errors": formal_case_lib_errors},
        }
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(state, attempt["attempt_id"], "annotation-main-check-formal-case-lib-contract")
        _append_event(run_root, state, "annotation-check-failed", reason="formal-case-lib-contract")
        _save_state(run_root, state)
        print(json.dumps({"status": "failed", "formal_case_lib_contract": formal_case_lib_errors}, indent=2))
        return 1
    source_version = _source_version_for_state(state, annotated=True)
    formal_case_lib_check = run_coqc_check(
        workspace_root=main_root,
        build_workspace=run_builds_root(run_root) / args.round / "formal-case-lib" / "src",
        target_file=Path(target["formal_case_lib"]),
        target_kind="formal-case-lib",
        source_goal_version=source_version["digest"],
    )
    formal_case_lib_check["controller_entrypoint"] = "annotation-check-round"
    if formal_case_lib_check.get("elapsed_seconds") is not None:
        _record_elapsed_stage(
            attempt,
            "formal-case-lib-coq-check",
            float(formal_case_lib_check["elapsed_seconds"]),
        )
    if formal_case_lib_check.get("status") != "passed":
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
            "symexec": {"status": symexec.get("status"), "returncode": symexec.get("returncode")},
            "diagnostics_split": {key: split.get(key) for key in ("manual_obligation_count", "diagnostic_count")},
            "formal_case_lib_coqc": {
                key: formal_case_lib_check.get(key)
                for key in ("status", "returncode", "first_diagnostic")
            },
        }
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(state, attempt["attempt_id"], "annotation-main-check-formal-case-lib-coqc")
        _append_event(run_root, state, "annotation-check-failed", reason="formal-case-lib-coqc")
        _save_state(run_root, state)
        print(
            json.dumps(
                {"status": "failed", "formal_case_lib_coqc": formal_case_lib_check},
                indent=2,
            )
        )
        return 1
    source_goal = _source_goal_version(state)
    state["source_version"] = source_version
    state["source_goal_version"] = source_goal
    attempt["status"] = "accepted"
    attempt["finished_at"] = _utc()
    attempt["main_check"] = {
        "symexec": {"status": symexec.get("status"), "returncode": symexec.get("returncode")},
        "diagnostics_split": {key: split.get(key) for key in ("manual_obligation_count", "diagnostic_count")},
        "formal_case_lib_coqc": {
            key: formal_case_lib_check.get(key)
            for key in ("status", "returncode")
        },
    }
    state["accepted_rounds"]["annotation"] = {
        "round": args.round,
        "attempt_id": attempt["attempt_id"],
        "annotation_history_directory": attempt["annotation_history_directory"],
        "source_version": source_version["digest"],
        "source_goal_version": source_goal["digest"],
    }
    _set_annotation_session_idle(state)
    state["phase"] = "annotation"
    state["next_actions"] = []
    _append_event(
        run_root,
        state,
        "annotation-round-accepted",
        round=args.round,
        source_goal_version=source_goal["digest"],
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "accepted",
                "source_version": source_version["digest"],
                "source_goal_version": source_goal["digest"],
                "target_witness_count": len(source_goal["target_witnesses"]),
            },
            indent=2,
        )
    )
    return 0


def _verify_group_plan(state: dict[str, Any], plan_path: Path) -> dict[str, Any]:
    plan = _json_load(plan_path, {})
    if not isinstance(plan, dict):
        raise SystemExit("group plan must be a JSON object")
    expected_goal = str(state["source_goal_version"]["digest"])
    targets = [str(item) for item in state["source_goal_version"]["target_witnesses"]]
    if plan.get("schema_version") != "qcp-vc-checking-group-plan/v3":
        raise SystemExit("group plan schema_version must be qcp-vc-checking-group-plan/v3")
    if plan.get("source_goal_version") != expected_goal:
        raise SystemExit("group plan source_goal_version is stale")
    groups = plan.get("groups")
    if not isinstance(groups, list) or not groups:
        raise SystemExit("group plan must contain non-empty groups")
    assigned: list[str] = []
    ids: set[str] = set()
    dependencies: dict[str, list[str]] = {}
    canonical_groups: list[dict[str, Any]] = []
    for group in groups:
        if not isinstance(group, dict) or not group.get("id"):
            raise SystemExit("each proof group requires id")
        group_id = str(group["id"])
        if group_id in ids:
            raise SystemExit(f"duplicate group_id: {group_id}")
        ids.add(group_id)
        witnesses = [str(item) for item in group.get("witnesses", [])]
        if not witnesses:
            raise SystemExit(f"proof group {group_id} has no witnesses")
        if len(witnesses) > int(state["max_witnesses_per_group"]):
            raise SystemExit(f"proof group {group_id} exceeds max_witnesses_per_group")
        assigned.extend(witnesses)
        dependencies[group_id] = [str(item) for item in group.get("depends_on", [])]
        canonical: dict[str, Any] = {
            "id": group_id,
            "witnesses": witnesses,
            "depends_on": dependencies[group_id],
        }
        if str(group.get("strategy") or "").strip():
            canonical["strategy"] = str(group["strategy"]).strip()
        helpers = group.get("helpers") if isinstance(group.get("helpers"), list) else []
        if helpers:
            canonical["helpers"] = [str(item) for item in helpers]
        canonical_groups.append(canonical)
    if len(assigned) != len(set(assigned)) or set(assigned) != set(targets):
        raise SystemExit("group plan must assign every target witness exactly once")
    for group_id, deps in dependencies.items():
        if group_id in deps or any(dep not in ids for dep in deps):
            raise SystemExit(f"invalid dependencies for group {group_id}")
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(group_id: str) -> None:
        if group_id in visiting:
            raise SystemExit("group dependency graph contains a cycle")
        if group_id in visited:
            return
        visiting.add(group_id)
        for dep in dependencies[group_id]:
            visit(dep)
        visiting.remove(group_id)
        visited.add(group_id)

    for group_id in dependencies:
        visit(group_id)
    plan = {
        "schema_version": "qcp-vc-checking-group-plan/v3",
        "source_goal_version": expected_goal,
        "groups": canonical_groups,
        "verified": True,
    }
    group_entries_from_plan(
        [{"name": name} for name in targets],
        plan,
        require_controller_verified=True,
        source_goal_version=expected_goal,
    )
    write_json(plan_path, plan)
    return plan


def vc_checking_check_round(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, "vc-checking")
    if attempt.get("status") != "ready-for-main-check":
        raise SystemExit("vc-checking attempt is not ready for main-owned checking")
    version_errors = _current_version_errors(state)
    if version_errors:
        raise SystemExit("vc-checking acceptance requires current annotation files: " + "; ".join(version_errors))
    expected_plan_path = (Path(str(attempt["report_directory"])) / "group_plan.json").resolve()
    plan_path = Path(args.group_plan).expanduser().resolve() if args.group_plan else expected_plan_path
    if plan_path != expected_plan_path:
        raise SystemExit(f"group_plan.json must use the current round report path: {expected_plan_path}")
    plan = _verify_group_plan(state, plan_path)
    attempt["status"] = "accepted"
    attempt["finished_at"] = _utc()
    attempt["group_plan"] = str(plan_path)
    state["accepted_rounds"]["vc-checking"] = {
        "round": args.round,
        "attempt_id": attempt["attempt_id"],
        "group_plan": str(plan_path),
        "source_goal_version": state["source_goal_version"]["digest"],
    }
    state["phase"] = "vc-checking"
    state["next_actions"] = []
    _append_event(run_root, state, "vc-checking-round-accepted", round=args.round)
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "accepted",
                "group_plan": str(plan_path),
                "groups": len(plan["groups"]),
            },
            indent=2,
        )
    )
    return 0
