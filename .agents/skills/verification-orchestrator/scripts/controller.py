#!/usr/bin/env python3
"""Single public CLI for the directory-based QCP verification workflow.

All user, main-agent, phase-agent, and group-worker operations enter through
this facade.  Focused internal modules implement run state, round lifecycle,
main-owned checks, vc-proving preparation/merge, and final checking; this file
parses public commands, dispatches them, and records the major timed stages
that belong to a concrete attempt or round.
"""

# ruff: noqa: E402 -- the standalone controller resolves internal module directories at runtime.

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parents[1] / "vc-proving" / "scripts"
if str(VC_PROVING_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from coq_tooling import run_coqc_check, run_coqtop_debug
from path_utils import run_builds_root
from symexec_tooling import run_symexec

from controller_final import final_apply, final_check
from controller_attempts import (
    ALLOWED_RESULT_STATUSES,
    _attempt_for_round,
    _group_tooling,
    mark_attempt_returned,
    mark_attempt_started,
    retry_round,
    review_attempt,
)
from controller_rounds import VC_PROVING_PHASE, annotation_summary_ready, spawn_instructions, step
from controller_state import (
    SCHEMA_RUN_LOG,
    SCHEMA_STATE,
    _json_load,
    _load_state,
    _record_elapsed_stage,
    _record_timing,
    _run_root_from_id,
    _save_state,
    init_run,
    timing_stage,
)
from controller_round_checks import (
    annotation_check_round,
    vc_checking_check_round,
)
from controller_proving import (
    vc_proving_preparing,
    vc_proving_verify,
)


DEFAULT_MAX_WITNESSES_PER_GROUP = 12
DEFAULT_MAX_COMPACT_ATTEMPTS = 3


def _command_context(args: argparse.Namespace) -> tuple[Path, Path, dict[str, Any]]:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    return main_root, run_root, _load_state(run_root)


def _group_manifest_entry(state: dict[str, Any], round_id: str, group_id: str) -> tuple[dict[str, Any], dict[str, Any]]:
    attempt = _attempt_for_round(state, round_id, VC_PROVING_PHASE)
    if attempt.get("status") != "groups-ready":
        raise SystemExit("group tooling requires the current groups-ready vc-proving round")
    current_goal = str(state.get("source_goal_version", {}).get("digest") or "")
    attempt_goal = str(attempt.get("source_goal_version") or "")
    if not current_goal or attempt_goal != current_goal:
        raise SystemExit("vc-proving round source_goal_version is stale")
    manifest = _json_load(Path(str(attempt["group_workers_manifest"])), {})
    groups = manifest.get("groups") if isinstance(manifest, dict) else None
    if not isinstance(groups, list):
        raise SystemExit("current vc-proving round has no group_workers_manifest groups")
    group = next((item for item in groups if str(item.get("id")) == group_id), None)
    if not isinstance(group, dict):
        raise SystemExit(f"group is not part of the current vc-proving round: {group_id}")
    if str(manifest.get("source_goal_version") or "") != current_goal:
        raise SystemExit("group source_goal_version is stale")
    return attempt, group


def symexec(args: argparse.Namespace) -> int:
    """Run canonical symbolic execution through the controller-owned entrypoint."""

    main_root, _run_root, state = _command_context(args)
    attempt = _attempt_for_round(state, args.round, "annotation")
    if attempt.get("status") in {"stale", "superseded"}:
        raise SystemExit("cannot run symbolic execution for a stale annotation round")
    evidence = run_symexec(
        main_root=main_root,
        target_c_file=Path(str(state["target_files"]["c_file"])),
        output_root=main_root,
    )
    evidence["controller_entrypoint"] = "symexec"
    evidence["controller_round"] = args.round
    if evidence.get("elapsed_seconds") is not None:
        _record_elapsed_stage(attempt, "symexec", float(evidence["elapsed_seconds"]))
        _save_state(Path(str(state["run_root"])), state)
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1


def coq_check(args: argparse.Namespace) -> int:
    """Run a derived Coq check without exposing path/flag assembly to callers."""

    main_root, run_root, state = _command_context(args)
    if args.target_kind == "formal-case-lib":
        attempt = _attempt_for_round(state, args.round, "annotation")
        if attempt.get("status") in {"stale", "superseded"}:
            raise SystemExit("cannot check formal_case_lib for a stale annotation round")
        if args.group is not None:
            raise SystemExit("--group is only valid for group-check")
        target_file = Path(str(state["target_files"]["formal_case_lib"]))
        build_workspace = run_builds_root(run_root) / args.round / "formal-case-lib" / "src"
        source_goal_version = str(attempt["source_version"])
        group_check_config = None
        overlays = None
    else:
        if not args.group:
            raise SystemExit("group-check requires --group")
        attempt, group = _group_manifest_entry(state, args.round, args.group)
        tooling = _group_tooling(state, attempt, group)
        target_file = tooling["target_file"]
        build_workspace = tooling["build_workspace"]
        source_goal_version = str(state["source_goal_version"]["digest"])
        group_check_config = tooling["group_check"]
        overlays = tooling["overlays"]
    evidence = run_coqc_check(
        workspace_root=main_root,
        build_workspace=build_workspace,
        target_file=target_file,
        target_kind=args.target_kind,
        source_goal_version=source_goal_version,
        group_check=group_check_config,
        overlays=overlays,
    )
    evidence["controller_entrypoint"] = "coq-check"
    evidence["controller_round"] = args.round
    if evidence.get("elapsed_seconds") is not None:
        _record_elapsed_stage(
            attempt,
            "formal-case-lib-coq-check" if args.target_kind == "formal-case-lib" else "group-coq-check",
            float(evidence["elapsed_seconds"]),
        )
        _save_state(run_root, state)
    if args.group:
        evidence["controller_group"] = args.group
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1


def coq_debug(args: argparse.Namespace) -> int:
    """Run the current group's fixed coqtop debug command through controller."""

    main_root, _run_root, state = _command_context(args)
    attempt, group = _group_manifest_entry(state, args.round, args.group)
    tooling = _group_tooling(state, attempt, group)
    evidence = run_coqtop_debug(
        workspace_root=main_root,
        build_workspace=tooling["build_workspace"],
        debug_script=tooling["debug_script"],
        source_goal_version=str(state["source_goal_version"]["digest"]),
        overlays=tooling["overlays"],
    )
    evidence["controller_entrypoint"] = "coq-debug"
    evidence["controller_round"] = args.round
    evidence["controller_group"] = args.group
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1


def validate_artifact_payload(kind: str, payload: Any, *, path: Path | None = None) -> list[str]:
    errors: list[str] = []
    if kind == "run-log":
        if path is None or not path.is_file():
            return ["run-log validation requires an existing --path"]
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                errors.append(f"line {line_number}: {exc}")
                continue
            if record.get("schema_version") != SCHEMA_RUN_LOG or not record.get("event"):
                errors.append(f"line {line_number}: invalid run log record")
        return errors
    if not isinstance(payload, dict):
        return ["artifact must be a JSON object"]
    schemas = {
        "agent-report": {"qcp-agent-report/v3"},
        "group-worker-report": {"qcp-group-worker-report/v2"},
        "manifest": {
            "qcp-vc-proving-base-manifest/v2",
            "qcp-vc-proving-group-workers-manifest/v3",
        },
        "group-plan": {"qcp-vc-checking-group-plan/v3"},
        "merge-result": {"qcp-vc-proving-proving-merged-result/v2"},
        "controller-state": {SCHEMA_STATE},
    }
    if payload.get("schema_version") not in schemas.get(kind, set()):
        errors.append(f"invalid schema_version for {kind}")
    if (
        kind == "manifest"
        and payload.get("schema_version") == "qcp-vc-proving-group-workers-manifest/v3"
        and not isinstance(payload.get("groups"), list)
    ):
        errors.append("group workers manifest groups list is required")
    if kind == "group-plan" and not isinstance(payload.get("groups"), list):
        errors.append("group plan groups list is required")
    if kind == "group-worker-report":
        extra = set(payload) - {"schema_version", "status", "source_goal_version", "blockers"}
        if extra:
            errors.append(f"unsupported group report fields: {sorted(extra)}")
    if kind == "agent-report":
        annotation_fields = {"schema_version", "status", "changed_files", "checks", "blockers"}
        vc_fields = {"schema_version", "status", "source_goal_version", "blockers"}
        if not (set(payload) <= annotation_fields or set(payload) <= vc_fields):
            errors.append("agent report contains unsupported fields")
    if kind == "merge-result" and not isinstance(payload.get("candidate"), dict):
        errors.append("merge result candidate is required")
    return errors


def validate_artifact(args: argparse.Namespace) -> int:
    path = Path(args.path).expanduser().resolve()
    payload = None if args.kind == "run-log" else _json_load(path)
    errors = validate_artifact_payload(args.kind, payload, path=path)
    print(
        json.dumps(
            {
                "status": "valid" if not errors else "invalid",
                "errors": errors,
                "path": str(path),
            },
            indent=2,
        )
    )
    return 0 if not errors else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Controller for QCP verification runs.")
    parser.add_argument("--main-root", default=None)
    sub = parser.add_subparsers(dest="command", required=True)

    init = sub.add_parser("init-run")
    init.add_argument("--case", required=True)
    init.add_argument("--target-c-file", required=True)
    init.add_argument("--timestamp", default=None)
    init.add_argument("--max-compact-attempts", type=int, default=DEFAULT_MAX_COMPACT_ATTEMPTS)
    init.add_argument("--max-witnesses-per-group", type=int, default=DEFAULT_MAX_WITNESSES_PER_GROUP)
    init.add_argument("--problem-statement", default="")
    init.add_argument("--problem-statement-file", default=None)
    init.add_argument("--target-function", default="")
    init.add_argument("--expected-behavior", default="")
    init.add_argument("--input-output-contract", default="")
    init.add_argument("--spec-hint", action="append", default=[])
    init.add_argument("--preferred-hidden-property", action="append", default=[])
    init.add_argument("--forbidden-pattern", action="append", default=[])
    init.add_argument("--reference-case-hint", action="append", default=[])
    init.set_defaults(func=init_run)

    step_cmd = sub.add_parser("step")
    step_cmd.add_argument("--run", required=True)
    step_cmd.set_defaults(func=step)

    spawn = sub.add_parser("spawn-instructions")
    spawn.add_argument("--run", required=True)
    spawn.add_argument("--next-action", required=True)
    spawn.set_defaults(func=spawn_instructions)

    for name, function in (
        ("mark-attempt-started", mark_attempt_started),
        ("mark-attempt-returned", mark_attempt_returned),
    ):
        item = sub.add_parser(name)
        item.add_argument("--run", required=True)
        item.add_argument("--attempt", required=True)
        if name == "mark-attempt-returned":
            item.add_argument(
                "--result-status",
                choices=sorted(ALLOWED_RESULT_STATUSES),
                default="returned",
            )
        item.set_defaults(func=function)

    review = sub.add_parser("review-attempt")
    review.add_argument("--run", required=True)
    review.add_argument("--attempt", required=True)
    review.set_defaults(func=review_attempt)

    retry = sub.add_parser("retry-round")
    retry.add_argument("--run", required=True)
    retry.add_argument("--phase", choices=["annotation", "vc-checking"], required=True)
    retry.add_argument("--reason", required=True)
    retry.add_argument("--previous-attempt", required=True)
    retry.set_defaults(func=retry_round)

    summary_ready = sub.add_parser("annotation-summary-ready")
    summary_ready.add_argument("--run", required=True)
    summary_ready.add_argument("--attempt", required=True)
    summary_ready.set_defaults(func=annotation_summary_ready)

    timing = sub.add_parser("timing-stage")
    timing.add_argument("--run", required=True)
    timing.add_argument("--round", required=True)
    timing.add_argument("--stage", choices=["annotation-checking"], required=True)
    timing.add_argument("--event", choices=["start", "finish"], required=True)
    timing.set_defaults(func=timing_stage)

    annotation = sub.add_parser("annotation-check-round")
    annotation.add_argument("--run", required=True)
    annotation.add_argument("--round", required=True)
    annotation.set_defaults(func=annotation_check_round)

    vc_check = sub.add_parser("vc-checking-check-round")
    vc_check.add_argument("--run", required=True)
    vc_check.add_argument("--round", required=True)
    vc_check.add_argument("--group-plan", default=None)
    vc_check.set_defaults(func=vc_checking_check_round)

    prepare = sub.add_parser("vc-proving-preparing")
    prepare.add_argument("--run", required=True)
    prepare.add_argument("--round", required=True)
    prepare.set_defaults(func=vc_proving_preparing)

    verify = sub.add_parser("vc-proving-verify")
    verify.add_argument("--run", required=True)
    verify.add_argument("--round", required=True)
    verify.set_defaults(func=vc_proving_verify)

    symexec_cmd = sub.add_parser("symexec")
    symexec_cmd.add_argument("--run", required=True)
    symexec_cmd.add_argument("--round", required=True)
    symexec_cmd.set_defaults(func=symexec)

    coq_check_cmd = sub.add_parser("coq-check")
    coq_check_cmd.add_argument("--run", required=True)
    coq_check_cmd.add_argument("--round", required=True)
    coq_check_cmd.add_argument("--target-kind", choices=["formal-case-lib", "group-check"], required=True)
    coq_check_cmd.add_argument("--group", default=None)
    coq_check_cmd.set_defaults(func=coq_check)

    coq_debug_cmd = sub.add_parser("coq-debug")
    coq_debug_cmd.add_argument("--run", required=True)
    coq_debug_cmd.add_argument("--round", required=True)
    coq_debug_cmd.add_argument("--group", required=True)
    coq_debug_cmd.set_defaults(func=coq_debug)

    apply_cmd = sub.add_parser("final-apply")
    apply_cmd.add_argument("--run", required=True)
    apply_cmd.set_defaults(func=final_apply)

    final = sub.add_parser("final-check")
    final.add_argument("--run", required=True)
    final.set_defaults(func=final_check)

    validate = sub.add_parser("validate-artifact")
    validate.add_argument(
        "--kind",
        choices=[
            "agent-report",
            "group-worker-report",
            "manifest",
            "group-plan",
            "merge-result",
            "controller-state",
            "run-log",
        ],
        required=True,
    )
    validate.add_argument("--path", required=True)
    validate.set_defaults(func=validate_artifact)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    started = time.monotonic()
    started_at = datetime.now(timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z")
    try:
        result = int(args.func(args))
    finally:
        if args.command not in {"init-run", "symexec", "coq-check", "timing-stage"} and getattr(args, "run", None):
            main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
            try:
                run_root = _run_root_from_id(main_root, args.run)
                _record_timing(
                    run_root,
                    args.command,
                    started_at=started_at,
                    elapsed_seconds=time.monotonic() - started,
                    round_id=getattr(args, "round", None),
                    attempt_id=getattr(args, "attempt", None),
                )
            except SystemExit:
                pass
    return result


if __name__ == "__main__":
    raise SystemExit(main())
