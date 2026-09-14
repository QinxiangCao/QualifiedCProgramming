"""Controller-owned symexec, Rocq check, and Rocq debug application services."""

from __future__ import annotations

import argparse
import copy
import json
from collections.abc import Callable
from pathlib import Path
from typing import Any

from annotation_refresh import (
    AnnotationRefreshError,
    begin_generated_refresh,
    commit_generated_refresh,
    rollback_generated_refresh,
)
from controller_attempts import (
    _attempt_for_round,
    _execute_group_check,
    _group_tooling,
    _proving_manifest_errors,
)
from controller_control import control_signal_path, control_signal_requests_stop
from controller_rounds import VC_PROVING_PHASE
from controller_state import (
    _annotation_snapshot_relatives,
    _annotation_before_snapshot_errors,
    _current_files_errors,
    _formal_case_lib_is_active,
    _formal_case_lib_snapshot,
    _generated_artifact_module_spellings_for_state,
    _load_state,
    _record_attempt_elapsed,
    _record_elapsed_stage,
    _run_root_from_id,
    _save_state,
    _snapshot_digests,
    _state_transaction,
    _utc,
    _validated_annotation_attempt_paths,
)
from coq_tooling import (
    compact_dune_preparation,
    prepare_dune_dependencies,
    run_coqc_check,
    run_coqtop_debug,
)
from path_utils import run_builds_root
from prepare_group_workers import resolve_group_workers_manifest
from proof_manual_utils import lib_contract_errors
from spec_freeze import annotation_spec_source_digest
from symexec_tooling import (
    _snapshot_text,
    run_symexec,
    symexec_profile_for_state,
)


def _command_context(args: argparse.Namespace) -> tuple[Path, Path, dict[str, Any]]:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    return main_root, run_root, _load_state(run_root)


def _group_manifest_entry(
    state: dict[str, Any],
    round_id: str,
    group_id: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    attempt = _attempt_for_round(state, round_id, VC_PROVING_PHASE)
    if attempt.get("status") != "groups-ready":
        raise SystemExit(
            "group tooling requires the current groups-ready vc-proving round"
        )
    manifest_errors = _proving_manifest_errors(state, attempt)
    if manifest_errors:
        raise SystemExit(
            "group tooling manifest integrity failed: " + "; ".join(manifest_errors)
        )
    manifest = resolve_group_workers_manifest(
        Path(str(attempt["group_workers_manifest"])),
        main_root=Path(str(state["main_root"])),
        expected_run_root=Path(str(state["run_root"])),
        expected_round=str(attempt["round"]),
    )
    groups = manifest.get("groups") if isinstance(manifest, dict) else None
    if not isinstance(groups, list):
        raise SystemExit(
            "current vc-proving round has no group_workers_manifest groups"
        )
    group = next((item for item in groups if str(item.get("id")) == group_id), None)
    if not isinstance(group, dict):
        raise SystemExit(
            f"group is not part of the current vc-proving round: {group_id}"
        )
    return attempt, group


def _require_running_group_delivery(
    attempt: dict[str, Any],
    group_id: str,
    *,
    operation: str,
) -> dict[str, Any]:
    group_state = attempt.get("groups", {}).get(group_id)
    delivery = group_state.get("delivery") if isinstance(group_state, dict) else None
    if (
        not isinstance(group_state, dict)
        or group_state.get("status") != "running"
        or not isinstance(delivery, dict)
        or not str(delivery.get("owner") or "")
    ):
        raise SystemExit(
            f"{operation} requires a currently claimed, running group delivery"
        )
    return group_state


def _annotation_symexec_failure(
    state: dict[str, Any],
    failure: dict[str, str],
) -> dict[str, Any]:
    return {
        "target_c_file": str(state["target_files"]["c_file"]),
        "status": "failed",
        "returncode": None,
        "generated_files": [],
        "first_failure": failure,
    }


def _finish_annotation_symexec(
    *,
    args: argparse.Namespace,
    evidence: dict[str, Any],
) -> int:
    evidence["controller_entrypoint"] = "symexec"
    evidence["controller_round"] = args.round
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1


_ANNOTATION_SYMEXEC_ATTEMPT_FIELDS = (
    "attempt_id",
    "round",
    "phase",
    "status",
    "report_directory",
    "annotation_history_directory",
    "before_snapshot",
    "owner",
    "delivery",
)


def _annotation_symexec_token(
    state: dict[str, Any],
    attempt: dict[str, Any],
) -> dict[str, Any]:
    return {
        "target_files": copy.deepcopy(state.get("target_files")),
        "formal_input_digest": annotation_spec_source_digest(
            Path(str(state["main_root"]))
            / str(state["target_files"]["c_file"]),
            Path(str(state["main_root"]))
            / str(state["target_files"]["formal_case_lib"]),
        ),
        "attempt": {
            field: copy.deepcopy(attempt.get(field))
            for field in _ANNOTATION_SYMEXEC_ATTEMPT_FIELDS
        },
    }


def _fresh_annotation_symexec_attempt(
    state: dict[str, Any],
    args: argparse.Namespace,
    token: dict[str, Any],
) -> tuple[dict[str, Any] | None, str | None]:
    if state.get("target_files") != token.get("target_files"):
        return None, "controller target_files changed during symbolic execution"
    try:
        attempt = _attempt_for_round(state, args.round, "annotation")
    except SystemExit as exc:
        return None, str(exc)
    expected = token.get("attempt")
    if not isinstance(expected, dict):
        return None, "symbolic-execution attempt token is invalid"
    for field in _ANNOTATION_SYMEXEC_ATTEMPT_FIELDS:
        if attempt.get(field) != expected.get(field):
            return None, f"annotation attempt {field} changed during symbolic execution"
    current_formal_digest = annotation_spec_source_digest(
        Path(str(state["main_root"])) / str(state["target_files"]["c_file"]),
        Path(str(state["main_root"]))
        / str(state["target_files"]["formal_case_lib"]),
    )
    if current_formal_digest != token.get("formal_input_digest"):
        return None, "annotation C or formal_case_lib changed during symbolic execution"
    try:
        _validated_annotation_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        return None, str(exc)
    if attempt.get("status") in {"stale", "superseded"}:
        return None, "annotation attempt became stale during symbolic execution"
    return attempt, None


def _complete_annotation_symexec(
    *,
    args: argparse.Namespace,
    main_root: Path,
    run_root: Path,
    token: dict[str, Any],
    evidence: dict[str, Any],
    refresh_preparation: dict[str, Any] | None,
) -> int:
    """Finalize generated refresh and timing against a fresh state generation."""

    with _state_transaction(run_root):
        state = _load_state(run_root)
        attempt, state_error = _fresh_annotation_symexec_attempt(
            state,
            args,
            token,
        )
        if state_error is not None:
            if refresh_preparation is not None:
                try:
                    rollback_generated_refresh(
                        main_root=main_root,
                        target_files=token["target_files"],
                        report_directory=Path(
                            str(token["attempt"]["report_directory"])
                        ),
                    )
                except AnnotationRefreshError as exc:
                    evidence["first_failure"] = exc.failure()
                    evidence["generated_refresh"] = {
                        **refresh_preparation,
                        "status": "rollback-failed",
                        "trigger_failure_kind": "annotation-symexec-state-drift",
                    }
                else:
                    evidence["first_failure"] = {
                        "category": "freshness",
                        "kind": "annotation-symexec-state-drift",
                        "message": state_error,
                        "repair": (
                            "Follow the current controller action; do not commit "
                            "generated output for the superseded annotation delivery."
                        ),
                    }
                    evidence["generated_refresh"] = {
                        **refresh_preparation,
                        "status": "rolled-back",
                        "trigger_failure_kind": "annotation-symexec-state-drift",
                    }
            else:
                evidence["first_failure"] = {
                    "category": "freshness",
                    "kind": "annotation-symexec-state-drift",
                    "message": state_error,
                    "repair": (
                        "Follow the current controller action before rerunning "
                        "symbolic execution."
                    ),
                }
            evidence["status"] = "failed"
            return _finish_annotation_symexec(args=args, evidence=evidence)

        if refresh_preparation is not None:
            if evidence.get("status") == "passed":
                try:
                    commit_generated_refresh(
                        target_files=token["target_files"],
                        report_directory=Path(
                            str(token["attempt"]["report_directory"])
                        ),
                    )
                except AnnotationRefreshError as exc:
                    evidence["status"] = "failed"
                    evidence["first_failure"] = exc.failure()
                    evidence["generated_refresh"] = {
                        **refresh_preparation,
                        "status": "commit-failed",
                    }
                else:
                    evidence["generated_refresh"] = {
                        **refresh_preparation,
                        "status": "committed",
                    }
            else:
                trigger = evidence.get("first_failure") or {}
                try:
                    rollback_generated_refresh(
                        main_root=main_root,
                        target_files=token["target_files"],
                        report_directory=Path(
                            str(token["attempt"]["report_directory"])
                        ),
                    )
                except AnnotationRefreshError as exc:
                    evidence["first_failure"] = exc.failure()
                    evidence["generated_refresh"] = {
                        **refresh_preparation,
                        "status": "rollback-failed",
                        "trigger_failure_kind": str(
                            trigger.get("kind") or "unknown"
                        ),
                    }
                else:
                    evidence["generated_refresh"] = {
                        **refresh_preparation,
                        "status": "rolled-back",
                        "trigger_failure_kind": str(
                            trigger.get("kind") or "unknown"
                        ),
                    }

        assert attempt is not None
        failure = evidence.get("first_failure")
        invocation = {
            "sequence": len(attempt.get("owner_symexec_invocations", [])) + 1,
            "recorded_at": _utc(),
            "status": str(evidence.get("status") or "failed"),
            "returncode": evidence.get("returncode"),
            "formal_input_digest": str(token.get("formal_input_digest") or ""),
            "elapsed_seconds": float(evidence.get("elapsed_seconds") or 0.0),
            "performance_profile": str(
                evidence.get("performance_profile") or "unknown"
            ),
            "timeout_seconds": evidence.get("timeout_seconds"),
            **(
                {
                    "failure_category": str(failure.get("category") or ""),
                    "failure_kind": str(failure.get("kind") or ""),
                }
                if isinstance(failure, dict)
                else {}
            ),
        }
        attempt.setdefault("owner_symexec_invocations", []).append(invocation)
        if (
            evidence.get("status") == "passed"
            and (evidence.get("generated_refresh") or {}).get("status")
            == "committed"
        ):
            try:
                target_digests = _snapshot_digests(
                    main_root,
                    _annotation_snapshot_relatives(state),
                )
            except (OSError, ValueError):
                attempt.pop("owner_generation_receipt", None)
            else:
                attempt["owner_generation_receipt"] = {
                    "status": "passed",
                    "attempt_id": str(attempt["attempt_id"]),
                    "round": str(attempt["round"]),
                    "formal_input_digest": str(
                        token.get("formal_input_digest") or ""
                    ),
                    "target_digests": target_digests,
                    "performance_profile": str(
                        evidence.get("performance_profile") or "unknown"
                    ),
                    "timeout_seconds": evidence.get("timeout_seconds"),
                    "elapsed_seconds": evidence.get("elapsed_seconds"),
                    "recorded_at": _utc(),
                }

        if evidence.get("elapsed_seconds") is not None:
            _record_elapsed_stage(
                attempt,
                "owner-generation",
                float(evidence["elapsed_seconds"]),
            )
        _save_state(run_root, state)
    return _finish_annotation_symexec(args=args, evidence=evidence)


def _symexec_for_annotation_attempt(
    *,
    args: argparse.Namespace,
    main_root: Path,
    run_root: Path,
    state: dict[str, Any],
    snapshot_errors: list[str],
    symexec_runner: Callable[..., dict[str, Any]] = run_symexec,
) -> int:
    attempt = _attempt_for_round(state, args.round, "annotation")
    try:
        attempt_paths = _validated_annotation_attempt_paths(state, attempt)
    except (OSError, ValueError) as exc:
        evidence = _annotation_symexec_failure(
            state,
            {
                "category": "structure",
                "kind": "annotation-attempt-path-topology",
                "message": str(exc),
                "repair": (
                    "Restore the controller-owned annotation attempt report and "
                    "history paths, then rerun the unchanged controller command."
                ),
            },
        )
        return _finish_annotation_symexec(args=args, evidence=evidence)
    token = _annotation_symexec_token(state, attempt)
    if attempt.get("status") in {"stale", "superseded"}:
        raise SystemExit("cannot run symbolic execution for a stale annotation round")
    previous_invocations = attempt.get("owner_symexec_invocations")
    previous_invocation = (
        previous_invocations[-1]
        if isinstance(previous_invocations, list) and previous_invocations
        else None
    )
    if (
        isinstance(previous_invocation, dict)
        and previous_invocation.get("failure_category") == "tool"
        and previous_invocation.get("formal_input_digest")
        != token.get("formal_input_digest")
    ):
        evidence = _annotation_symexec_failure(
            state,
            {
                "category": "contract",
                "kind": "tool-retry-formal-input-drift",
                "message": (
                    "annotation C/formal_case_lib changed after the first tool "
                    "failure; the one permitted tooling retry must use the exact "
                    "same formal input"
                ),
                "repair": (
                    "Restore the formal bytes used by the first failed invocation "
                    "and rerun the unchanged controller symexec command."
                ),
            },
        )
        return _finish_annotation_symexec(args=args, evidence=evidence)

    if snapshot_errors:
        evidence = _annotation_symexec_failure(
            state,
            {
                "category": "structure",
                "kind": "annotation-before-snapshot-integrity",
                "message": snapshot_errors[0],
                "repair": (
                    "Restore the immutable controller-owned attempt before snapshot "
                    "before refreshing generated files; do not recreate it from the "
                    "current edited main root."
                ),
            },
        )
        return _complete_annotation_symexec(
            args=args,
            main_root=main_root,
            run_root=run_root,
            token=token,
            evidence=evidence,
            refresh_preparation=None,
        )

    try:
        refresh_preparation = begin_generated_refresh(
            main_root=main_root,
            target_files=state["target_files"],
            report_directory=attempt_paths["directory"],
        )
    except AnnotationRefreshError as exc:
        evidence = _annotation_symexec_failure(state, exc.failure())
        evidence["generated_refresh"] = {"status": "not-started"}
        return _complete_annotation_symexec(
            args=args,
            main_root=main_root,
            run_root=run_root,
            token=token,
            evidence=evidence,
            refresh_preparation=None,
        )

    try:
        profile = symexec_profile_for_state(state)
        signal_path = control_signal_path(state)
        evidence = symexec_runner(
            main_root=main_root,
            target_c_file=Path(str(state["target_files"]["c_file"])),
            target_files=state["target_files"],
            output_root=main_root,
            timeout_seconds=float(profile["timeout_seconds"]),
            profile_name=str(profile["name"]),
            heartbeat_seconds=float(profile["heartbeat_seconds"]),
            poll_interval_seconds=float(profile["poll_interval_seconds"]),
            cancel_requested=lambda: control_signal_requests_stop(signal_path),
            progress_path=attempt_paths["directory"] / "symexec-progress-owner.json",
        )
    except (OSError, RuntimeError, ValueError) as exc:
        evidence = _annotation_symexec_failure(
            state,
            {
                "category": "tool",
                "kind": "annotation-main-symexec-invocation",
                "message": str(exc),
                "repair": (
                    "Repair the controller-selected symbolic-execution environment "
                    "and rerun the unchanged controller symexec command."
                ),
            },
        )
    return _complete_annotation_symexec(
        args=args,
        main_root=main_root,
        run_root=run_root,
        token=token,
        evidence=evidence,
        refresh_preparation=refresh_preparation,
    )


def symexec(
    args: argparse.Namespace,
    *,
    symexec_runner: Callable[..., dict[str, Any]] = run_symexec,
) -> int:
    """Run one transactional annotation symbolic-execution refresh."""

    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    with _state_transaction(run_root):
        state = _load_state(run_root)
        attempt = _attempt_for_round(state, args.round, "annotation")
        if attempt.get("status") in {"stale", "superseded"}:
            raise SystemExit(
                "cannot run symbolic execution for a stale annotation round"
            )
        snapshot_errors = _annotation_before_snapshot_errors(state, attempt)
    return _symexec_for_annotation_attempt(
        args=args,
        main_root=main_root,
        run_root=run_root,
        state=state,
        snapshot_errors=snapshot_errors,
        symexec_runner=symexec_runner,
    )


def coq_check(
    args: argparse.Namespace,
    *,
    coq_check_runner: Callable[..., dict[str, Any]] = run_coqc_check,
) -> int:
    """Run a derived Coq check without exposing path/flag assembly to callers."""

    main_root, run_root, state = _command_context(args)
    evidence: dict[str, Any] | None = None
    dune_preparation: dict[str, Any] | None = None
    formal_case_lib_target = args.target_kind in {
        "formal-case-lib-design",
        "formal-case-lib",
    }
    design_mode = args.target_kind == "formal-case-lib-design"
    if formal_case_lib_target:
        attempt = _attempt_for_round(state, args.round, "annotation")
        if attempt.get("status") in {"stale", "superseded"}:
            raise SystemExit(
                "cannot check formal_case_lib for a stale annotation round"
            )
        if args.group is not None:
            raise SystemExit("--group is only valid for group-check")
        target_file = Path(str(state["target_files"]["formal_case_lib"]))
        build_workspace = (
            run_builds_root(run_root)
            / args.round
            / (
                "formal-case-lib-design"
                if design_mode
                else "formal-case-lib"
            )
            / "src"
        )
        group_check_config = None
        overlays = None
        formal_case_lib_active = _formal_case_lib_is_active(state)
        formal_case_lib_snapshot = _formal_case_lib_snapshot(state)
        formal_case_lib_state = str(
            formal_case_lib_snapshot.get("state") or "invalid"
        )
        if not formal_case_lib_active and formal_case_lib_state == "missing":
            evidence = {
                "status": "passed",
                "skipped": True,
                "reason": "optional formal_case_lib candidate is absent",
                "target_file": str(target_file),
                "returncode": None,
            }
        elif not formal_case_lib_active:
            topology_detail = str(
                formal_case_lib_snapshot.get("message")
                or "candidate path is present"
            )
            evidence = {
                "status": "failed",
                "skipped": False,
                "target_file": str(target_file),
                "returncode": 2,
                "first_failure": {
                    "category": "freshness",
                    "kind": "inactive-formal-case-lib-created",
                    "message": (
                        "formal_case_lib is absent from the fixed run topology but "
                        "the read-only candidate path is not truly absent: "
                        f"{topology_detail}"
                    ),
                    "repair": (
                        "Restore the candidate path to its sealed missing state; "
                        "do not create a placeholder or new case lib."
                    ),
                },
            }
        else:
            try:
                formal_case_lib_text = _snapshot_text(
                    formal_case_lib_snapshot,
                    label="formal_case_lib candidate",
                )
                formal_case_lib_errors = lib_contract_errors(
                    formal_case_lib_text,
                    forbidden_modules=(
                        _generated_artifact_module_spellings_for_state(state)
                    ),
                )
            except (OSError, UnicodeError, ValueError) as exc:
                formal_case_lib_errors = [
                    f"formal_case_lib contract could not be evaluated: {exc}"
                ]
            if formal_case_lib_errors:
                evidence = {
                    "status": "failed",
                    "skipped": False,
                    "target_file": str(target_file),
                    "returncode": 2,
                    "first_failure": {
                        "category": "contract",
                        "kind": "formal-case-lib-contract",
                        "message": formal_case_lib_errors[0],
                        "repair": (
                            "Repair the formal_case_lib safety or exact current "
                            "generated-module import violation, then rerun the "
                            "unchanged controller command."
                        ),
                    },
                    "contract_errors": formal_case_lib_errors,
                }
    else:
        if not args.group:
            raise SystemExit("group-check requires --group")
        attempt, _group = _group_manifest_entry(state, args.round, args.group)
        _require_running_group_delivery(
            attempt,
            args.group,
            operation=args.target_kind,
        )
        evidence = _execute_group_check(
            state,
            attempt,
            args.group,
            development=args.target_kind == "group-development",
        )
        evidence.pop("validation", None)
    if evidence is None:
        if formal_case_lib_target:
            # The owner may have changed formal_case_lib imports. Ask the
            # selected backend to prepare that exact target immediately before
            # the local coqc check. This annotation-time receipt never changes
            # the accepted run dependency snapshot.
            dune_preparation = prepare_dune_dependencies(
                workspace_root=main_root,
                target_file=target_file,
                current_case_anchor=(
                    target_file
                    if design_mode
                    else Path(str(state["target_files"]["proof_auto_file"]))
                ),
            )
            if dune_preparation.get("status") != "passed":
                evidence = {
                    "status": "failed",
                    "target_file": str(target_file),
                    "target_kind": args.target_kind,
                    "build_workspace": str(build_workspace),
                    "returncode": 2,
                    "first_failure": dune_preparation.get("first_failure"),
                    "dune_preparation": dune_preparation,
                }
        if evidence is None:
            evidence = coq_check_runner(
                workspace_root=main_root,
                build_workspace=build_workspace,
                target_file=target_file,
                target_kind=args.target_kind,
                group_check=group_check_config,
                overlays=overlays,
                current_case_anchor=(
                    target_file
                    if design_mode
                    else Path(str(state["target_files"]["proof_auto_file"]))
                ),
                dune_preparation=dune_preparation,
            )
    if formal_case_lib_target and dune_preparation is not None:
        evidence["dune_preparation"] = compact_dune_preparation(dune_preparation)
    evidence["controller_entrypoint"] = "coq-check"
    evidence["controller_round"] = args.round
    if evidence.get("elapsed_seconds") is not None:
        _record_attempt_elapsed(
            run_root,
            attempt_id=str(attempt["attempt_id"]),
            stage=(
                "formal-case-lib-design-coq-check"
                if design_mode
                else "formal-case-lib-coq-check"
                if args.target_kind == "formal-case-lib"
                else "group-development-check"
                if args.target_kind == "group-development"
                else "group-coq-check"
            ),
            elapsed_seconds=float(evidence["elapsed_seconds"]),
        )
    evidence["controller_entrypoint"] = "coq-check"
    evidence["controller_round"] = args.round
    if args.group:
        evidence["controller_group"] = args.group
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1


def coq_debug(
    args: argparse.Namespace,
    *,
    coq_debug_runner: Callable[..., dict[str, Any]] = run_coqtop_debug,
) -> int:
    """Inspect the active VC manual or run one group worker debug command."""

    main_root, run_root, state = _command_context(args)
    if args.group:
        attempt, group = _group_manifest_entry(state, args.round, args.group)
        _require_running_group_delivery(
            attempt,
            args.group,
            operation="group coq-debug",
        )
        tooling = _group_tooling(state, attempt, group)
        build_workspace = tooling["build_workspace"]
        debug_script = tooling["debug_script"]
        overlays = tooling["overlays"]
    else:
        attempt = _attempt_for_round(state, args.round, "vc-checking")
        if attempt.get("status") != "running":
            raise SystemExit("manual goal inspection requires an active vc-checking delivery")
        file_errors = _current_files_errors(state)
        if file_errors:
            raise SystemExit("current main-root files changed: " + file_errors[0])
        build_workspace = run_builds_root(run_root) / args.round / "vc-checking" / "src"
        debug_script = Path(str(state["target_files"]["proof_manual_file"]))
        overlays = None
    debug_path = build_workspace / debug_script
    evidence = coq_debug_runner(
        workspace_root=main_root,
        build_workspace=build_workspace,
        debug_script=debug_script,
        overlays=overlays,
        current_case_anchor=Path(str(state["target_files"]["proof_auto_file"])),
    )
    authorized_script = str(debug_path)
    if evidence.get("status") == "passed" and (
        evidence.get("debug_script_path") != authorized_script
        or evidence.get("load_argument") != authorized_script
        or evidence.get("resolved_script_path") != authorized_script
        or evidence.get("resolved_matches_authorized") is not True
    ):
        evidence.update(
            {
                "status": "failed",
                "returncode": 2,
                "first_failure": {
                    "category": "contract",
                    "kind": "debug-script-path-resolution",
                    "message": (
                        "coqtop result is not bound to the controller-authorized "
                        "debug script path"
                    ),
                    "repair": (
                        "Use the validated absolute debug script as the coqtop "
                        "load argument."
                    ),
                },
            }
        )
    evidence["controller_entrypoint"] = "coq-debug"
    evidence["controller_round"] = args.round
    if args.group:
        evidence["controller_group"] = args.group
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1
