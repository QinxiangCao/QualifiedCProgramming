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
from controller_rounds import VC_PROVING_PHASE, _latest_reusable_vc_proving_round
from controller_state import (
    _annotation_before_snapshot_errors,
    _append_event,
    _current_version_errors,
    _debug_build_snapshot,
    _file_digest,
    _formal_case_lib_is_active,
    _formal_case_lib_snapshot,
    _generated_artifact_module_spellings_for_state,
    _load_state,
    _record_attempt_elapsed,
    _record_elapsed_stage,
    _run_root_from_id,
    _state_transaction,
    _save_state,
    _validated_annotation_attempt_paths,
    _verified_reuse_source_build,
)
from coq_tooling import (
    compact_dune_preparation,
    dune_snapshot_for_preserved_build,
    prepare_dune_dependencies,
    run_coqc_check,
    run_coqtop_debug,
)
from path_utils import (
    reuse_source_build_workspace,
    run_builds_root,
    vc_checking_build_workspace,
    vc_checking_debug_script,
)
from prepare_group_workers import resolve_group_workers_manifest
from proof_manual_utils import (
    debug_goal_show_contract,
    lib_contract_errors,
    show_command_count,
)
from symexec_tooling import (
    _snapshot_text,
    run_symexec,
    source_goal_version_at_root,
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
    current_goal = str(state.get("source_goal_version", {}).get("digest") or "")
    attempt_goal = str(attempt.get("source_goal_version") or "")
    if not current_goal or attempt_goal != current_goal:
        raise SystemExit("vc-proving round source_goal_version is stale")
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
    if str(manifest.get("source_goal_version") or "") != current_goal:
        raise SystemExit("group source_goal_version is stale")
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
    "source_version",
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
                    # The generated roles are now committed on disk, so the run's
                    # source-goal version is well defined.  Persist it here rather
                    # than only at acceptance: selected-backend preparation and
                    # formal-case-lib checking both run before acceptance and
                    # are keyed on this digest. Computed after the
                    # commit so it hashes the files that are actually in place, and
                    # saved explicitly -- the `elapsed_seconds` branch below is
                    # conditional and cannot be relied on to flush this write.
                    state["source_goal_version"] = source_goal_version_at_root(
                        root=main_root,
                        target_files=state["target_files"],
                    )
                    _save_state(run_root, state)
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

        if evidence.get("elapsed_seconds") is not None:
            assert attempt is not None
            _record_elapsed_stage(
                attempt,
                "symexec",
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
            before_snapshot_directory=attempt_paths["before"],
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
        evidence = symexec_runner(
            main_root=main_root,
            target_c_file=Path(str(state["target_files"]["c_file"])),
            target_files=state["target_files"],
            output_root=main_root,
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
    if args.target_kind == "formal-case-lib":
        attempt = _attempt_for_round(state, args.round, "annotation")
        if attempt.get("status") in {"stale", "superseded"}:
            raise SystemExit(
                "cannot check formal_case_lib for a stale annotation round"
            )
        if args.group is not None:
            raise SystemExit("--group is only valid for group-check")
        target_file = Path(str(state["target_files"]["formal_case_lib"]))
        build_workspace = (
            run_builds_root(run_root) / args.round / "formal-case-lib" / "src"
        )
        # The annotation owner's canonical symexec refreshes this version before
        # the optional library check. It binds the ephemeral selected-backend
        # receipt and local coqc result to the same generated goal state.
        source_goal_version = str(
            (state.get("source_goal_version") or {}).get("digest") or ""
        )
        if not source_goal_version:
            raise SystemExit(
                "formal-case-lib check requires the current generated source_goal_version"
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
        source_goal_version = str(state["source_goal_version"]["digest"])
        evidence = _execute_group_check(
            state,
            attempt,
            args.group,
            development=args.target_kind == "group-development",
        )
        evidence.pop("validation", None)
    if evidence is None:
        if args.target_kind == "formal-case-lib":
            # The owner may have changed formal_case_lib imports. Ask the
            # selected backend to prepare that exact target immediately before
            # the local coqc check. This annotation-time receipt never changes
            # the accepted run dependency snapshot.
            dune_preparation = prepare_dune_dependencies(
                workspace_root=main_root,
                target_file=target_file,
                current_case_anchor=Path(
                    str(state["target_files"]["proof_auto_file"])
                ),
                source_goal_version=source_goal_version,
            )
            if dune_preparation.get("status") != "passed":
                evidence = {
                    "status": "failed",
                    "target_file": str(target_file),
                    "target_kind": args.target_kind,
                    "source_goal_version": source_goal_version,
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
                source_goal_version=source_goal_version,
                group_check=group_check_config,
                overlays=overlays,
                current_case_anchor=Path(str(state["target_files"]["proof_auto_file"])),
                dune_preparation=dune_preparation,
            )
    if args.target_kind == "formal-case-lib" and dune_preparation is not None:
        evidence["dune_preparation"] = compact_dune_preparation(dune_preparation)
    evidence["controller_entrypoint"] = "coq-check"
    evidence["controller_round"] = args.round
    if evidence.get("elapsed_seconds") is not None:
        _record_attempt_elapsed(
            run_root,
            attempt_id=str(attempt["attempt_id"]),
            stage=(
                "formal-case-lib-coq-check"
                if args.target_kind == "formal-case-lib"
                else "group-development-check"
                if args.target_kind == "group-development"
                else "group-coq-check"
            ),
            elapsed_seconds=float(evidence["elapsed_seconds"]),
        )
    if args.group:
        evidence["controller_group"] = args.group
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1


def _active_reuse_vc_attempt(
    state: dict[str, Any],
    reference_round: str,
) -> dict[str, Any]:
    matches = [
        attempt
        for attempt in reversed(list(state.get("attempts", {}).values()))
        if attempt.get("phase") == "vc-checking"
        and attempt.get("proof_reuse_round") == reference_round
        and attempt.get("status") not in {"accepted", "stale", "superseded"}
    ]
    if len(matches) != 1:
        raise SystemExit(
            "previous-goal debug requires exactly one active vc-checking reuse attempt"
        )
    return matches[0]


def _show_command_count(debug_script: Path) -> int:
    if not debug_script.is_file():
        raise SystemExit(f"debug script is missing: {debug_script}")
    debug_files = {
        item.resolve() for item in debug_script.parent.rglob("*") if item.is_file()
    }
    if debug_files != {debug_script.resolve()}:
        raise SystemExit(
            "current/previous VC debug directory must contain only the declared script"
        )
    script_text = debug_script.read_text(encoding="utf-8")
    errors, _shown = debug_goal_show_contract(script_text)
    if errors:
        raise SystemExit(
            "current/previous VC debug script violates the inspection contract: "
            + "; ".join(errors)
        )
    return show_command_count(script_text)


def _current_vc_debug_context(
    *,
    main_root: Path,
    run_root: Path,
    state: dict[str, Any],
    round_id: str,
    coq_check_runner: Callable[..., dict[str, Any]],
) -> tuple[
    dict[str, Any],
    Path,
    Path,
    str,
    dict[str, Any] | None,
]:
    attempt = _attempt_for_round(state, round_id, "vc-checking")
    if attempt.get("status") in {"stale", "superseded", "accepted"}:
        raise SystemExit("current VC debug requires an active vc-checking attempt")
    version_errors = _current_version_errors(state)
    if version_errors:
        raise SystemExit(
            "current VC debug requires current accepted annotation files: "
            + "; ".join(version_errors)
        )
    build_workspace = vc_checking_build_workspace(run_root, round_id)
    debug_script = vc_checking_debug_script(run_root, round_id).relative_to(
        build_workspace
    )
    source_goal_version = str(state["source_goal_version"]["digest"])
    prepare = coq_check_runner(
        workspace_root=main_root,
        build_workspace=build_workspace,
        target_file=Path(str(state["target_files"]["proof_auto_file"])),
        target_kind="vc-checking-debug",
        source_goal_version=source_goal_version,
        current_case_anchor=Path(str(state["target_files"]["proof_auto_file"])),
    )
    return (
        attempt,
        build_workspace,
        debug_script,
        source_goal_version,
        prepare,
    )


def _sealed_reuse_debug_context(
    *,
    main_root: Path,
    run_root: Path,
    state: dict[str, Any],
    round_id: str,
) -> tuple[dict[str, Any], Path, Path, str, dict[str, Any], dict[str, Any]]:
    if _latest_reusable_vc_proving_round(state) != round_id:
        raise SystemExit(
            "previous VC debug is limited to the immediately preceding sealed "
            "reusable vc-proving round"
        )
    attempt = state["attempts"][round_id]
    build_workspace = reuse_source_build_workspace(run_root, round_id)
    source_goal_version = str(attempt.get("source_goal_version") or "")
    sealed_snapshot = attempt.get("reuse_source_snapshot")
    if not isinstance(sealed_snapshot, dict):
        raise SystemExit("previous vc-proving round lacks a sealed reuse-source build")
    try:
        validated_snapshot, _build = _verified_reuse_source_build(
            main_root=main_root,
            run_root=run_root,
            round_id=round_id,
            sealed=sealed_snapshot,
            source_goal_version=source_goal_version,
        )
    except (OSError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    return (
        _active_reuse_vc_attempt(state, round_id),
        build_workspace,
        Path(".coq_debug") / "reuse-source.v",
        source_goal_version,
        sealed_snapshot,
        validated_snapshot,
    )


def _record_reuse_debug_receipt(
    *,
    main_root: Path,
    run_root: Path,
    state: dict[str, Any],
    attempt: dict[str, Any],
    receipt_kind: str,
    source_round: str,
    build_workspace: Path,
    debug_script: Path,
    source_goal_version: str,
    show_count: int,
    sealed_reference_snapshot: dict[str, Any] | None,
) -> None:
    debug_path = build_workspace / debug_script
    try:
        if sealed_reference_snapshot is not None:
            _dependency_snapshot, snapshot = _verified_reuse_source_build(
                main_root=main_root,
                run_root=run_root,
                round_id=source_round,
                sealed=sealed_reference_snapshot,
                source_goal_version=source_goal_version,
            )
        else:
            snapshot = _debug_build_snapshot(
                build_workspace,
                dune_dependency_snapshot=dune_snapshot_for_preserved_build(
                    workspace_root=main_root,
                    receipt=state.get("dune_preparation"),
                ),
            )
    except (OSError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    attempt.setdefault("proof_reuse_debug", {})[receipt_kind] = {
        "status": "passed",
        "round": source_round,
        "source_goal_version": source_goal_version,
        "build_digest": snapshot["digest"],
        "build_file_count": snapshot["file_count"],
        "debug_script_sha256": _file_digest(debug_path),
        "show_count": show_count,
    }
    _append_event(
        run_root,
        state,
        "proof-reuse-debug-completed",
        round=str(attempt["round"]),
        debug_kind=receipt_kind,
        source_round=source_round,
    )
    _save_state(run_root, state)


def coq_debug(
    args: argparse.Namespace,
    *,
    coq_check_runner: Callable[..., dict[str, Any]] = run_coqc_check,
    coq_debug_runner: Callable[..., dict[str, Any]] = run_coqtop_debug,
) -> int:
    """Run a fixed group, current-VC, or sealed-reference Rocq debug command."""

    main_root, run_root, state = _command_context(args)
    receipt_attempt: dict[str, Any] | None = None
    receipt_kind: str | None = None
    sealed_reference_snapshot: dict[str, Any] | None = None
    reuse_dune_snapshot: dict[str, Any] | None = None
    overlays = None
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
        source_goal_version = str(state["source_goal_version"]["digest"])
        reuse_existing_build = False
    else:
        round_state = state.get("rounds", {}).get(args.round)
        if not isinstance(round_state, dict):
            raise SystemExit(f"debug round not found: {args.round}")
        phase = str(round_state.get("phase") or "")
        if phase == "vc-checking":
            (
                attempt,
                build_workspace,
                debug_script,
                source_goal_version,
                prepare,
            ) = _current_vc_debug_context(
                main_root=main_root,
                run_root=run_root,
                state=state,
                round_id=args.round,
                coq_check_runner=coq_check_runner,
            )
            if prepare is not None and prepare.get("status") != "passed":
                print(
                    json.dumps(
                        {"status": "failed", "prepare": prepare},
                        indent=2,
                        ensure_ascii=True,
                    )
                )
                return 1
            if attempt.get("proof_reuse_round"):
                receipt_attempt = attempt
                receipt_kind = "current"
            reuse_existing_build = True
        elif phase == VC_PROVING_PHASE:
            (
                receipt_attempt,
                build_workspace,
                debug_script,
                source_goal_version,
                sealed_reference_snapshot,
                reuse_dune_snapshot,
            ) = _sealed_reuse_debug_context(
                main_root=main_root,
                run_root=run_root,
                state=state,
                round_id=args.round,
            )
            receipt_kind = "reference"
            reuse_existing_build = True
        else:
            raise SystemExit(
                "coq-debug without --group is only valid for vc-checking or its "
                "sealed reusable proving source"
            )

    debug_path = build_workspace / debug_script
    show_count = _show_command_count(debug_path) if not args.group else 0
    evidence = coq_debug_runner(
        workspace_root=main_root,
        build_workspace=build_workspace,
        debug_script=debug_script,
        source_goal_version=source_goal_version,
        overlays=overlays,
        reuse_existing_build=reuse_existing_build,
        current_case_anchor=Path(str(state["target_files"]["proof_auto_file"])),
        _reuse_dune_snapshot=reuse_dune_snapshot,
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
    elif (
        evidence.get("status") == "passed"
        and receipt_attempt is not None
        and receipt_kind is not None
    ):
        _record_reuse_debug_receipt(
            main_root=main_root,
            run_root=run_root,
            state=state,
            attempt=receipt_attempt,
            receipt_kind=receipt_kind,
            source_round=args.round,
            build_workspace=build_workspace,
            debug_script=debug_script,
            source_goal_version=source_goal_version,
            show_count=show_count,
            sealed_reference_snapshot=sealed_reference_snapshot,
        )
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1
