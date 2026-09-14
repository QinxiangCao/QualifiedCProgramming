#!/usr/bin/env python3
"""Main-owned checks that accept annotation and vc-checking rounds.

This module is internal to controller.py.  It replays required tooling,
validates a round against current formal state, and records acceptance.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from annotation_refresh import (
    AnnotationRefreshError,
    begin_generated_refresh,
    commit_generated_refresh,
    rollback_generated_refresh,
)
from annotation_contract_lint import contract_surface_lint
from annotation_design import (
    annotation_plan_errors,
    annotation_plan_path,
)
from controller_attempts import (
    _artifact_integrity_errors,
    _attempt_for_round,
    _queue_annotation_feedback,
    _queue_vc_checking_retry,
    _transition_current_file_drift,
)
from controller_control import control_signal_path, control_signal_requests_stop
from controller_invocations import hydrate_actions
from controller_state import (
    _annotation_after_snapshot_errors,
    _annotation_snapshot_relatives,
    _append_event,
    _current_files_errors,
    _file_digest,
    _formal_case_lib_is_active,
    _formal_case_lib_snapshot,
    _generated_artifact_module_spellings_for_state,
    _json_load,
    _load_state,
    _manual_obligations,
    _proof_manual_sha256,
    _record_elapsed_stage,
    _run_root_from_id,
    _save_state,
    _snapshot_digests,
    _utc,
    _validated_annotation_attempt_paths,
)
from coq_tooling import (
    prepare_dune_dependencies,
    run_coqc_check,
)
from group_plan_utils import group_entries_from_plan
from path_utils import (
    fixed_path_under,
    run_builds_root,
)
from proof_manual_utils import (
    coq_token_text,
    ensure_unique_lemma_names,
    lemma_proof_parts,
    lib_contract_errors,
    parse_manual_file,
)
from spec_freeze import (
    annotation_spec_source_digest,
    extract_spec_surface,
    spec_freeze_findings,
)
from symexec_tooling import (
    _lexical_regular_file_snapshot,
    _snapshot_text,
    clean_output_freshness,
    run_symexec,
    symexec_profile_for_state,
)


def _set_annotation_session_idle(state: dict[str, Any]) -> None:
    session = state.get("annotation_session")
    if isinstance(session, dict):
        session["status"] = "idle"


def _update_user_spec_baseline(
    state: dict[str, Any], *, main_root: Path
) -> None:
    record = state.get("spec_freeze")
    if (
        not isinstance(record, dict)
        or not record.get("functions")
        or record.get("baseline") is not None
    ):
        return
    target = state["target_files"]
    record["baseline"] = extract_spec_surface(
        main_root / target["c_file"],
        main_root / target["formal_case_lib"],
    )


def _compact_symexec_evidence(symexec: dict[str, Any]) -> dict[str, Any]:
    return {
        key: symexec.get(key)
        for key in (
            "status",
            "returncode",
            "timeout_seconds",
            "elapsed_seconds",
            "performance_profile",
            "reused_owner_generation",
            "owner_generation_receipt",
            "first_failure",
        )
        if symexec.get(key) is not None
    }


def _compact_annotation_dune_evidence(evidence: dict[str, Any]) -> dict[str, Any]:
    """Keep exact annotation-time dependency preparation visible but ephemeral."""

    return {
        key: evidence.get(key)
        for key in (
            "status",
            "build_mode",
            "target",
            "returncode",
            "base_artifact_count",
            "current_source_count",
            "rebuilt_count",
            "dependency_metrics",
            "current_cleanup",
            "make_seconds",
            "elapsed_seconds",
            "first_failure",
        )
        if evidence.get(key) is not None
    }


def _manual_vc_signature(
    text: str,
) -> tuple[str, tuple[tuple[str, str, str, str], ...]]:
    """Ignore only temporary ``Show.`` commands in a VC-checking manual."""

    prelude, lemmas = parse_manual_file(text)
    ensure_unique_lemma_names(lemmas)
    declarations: list[tuple[str, str, str, str]] = []
    for lemma in lemmas:
        statement, proof, trailing = lemma_proof_parts(lemma)
        proof_tokens = coq_token_text(proof).splitlines()
        without_show: list[str] = []
        index = 0
        while index < len(proof_tokens):
            if proof_tokens[index : index + 2] == ["Show", "."]:
                index += 2
                continue
            without_show.append(proof_tokens[index])
            index += 1
        declarations.append(
            (
                str(lemma["name"]),
                coq_token_text(statement),
                "\n".join(without_show),
                coq_token_text(trailing),
            )
        )
    return coq_token_text(prelude), tuple(declarations)


def _current_manual_vc_signature(
    state: dict[str, Any],
) -> tuple[str, tuple[tuple[str, str, str, str], ...]] | None:
    relative = str(state["target_files"]["proof_manual_file"])
    snapshot = _lexical_regular_file_snapshot(
        root=Path(str(state["main_root"])),
        relative=relative,
        label="current proof manual",
    )
    if snapshot.get("state") == "missing":
        return None
    return _manual_vc_signature(
        _snapshot_text(snapshot, label="current proof manual")
    )


def _transactional_main_root_symexec(
    state: dict[str, Any],
    *,
    report_directory: Path,
    progress_name: str = "symexec-progress-main-refresh.json",
) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    target = state["target_files"]
    try:
        preparation = begin_generated_refresh(
            main_root=main_root,
            target_files=target,
            report_directory=report_directory,
        )
    except AnnotationRefreshError as exc:
        return {
            "status": "failed",
            "returncode": None,
            "first_failure": exc.failure(),
            "generated_refresh": {"status": "not-started"},
        }
    try:
        profile = symexec_profile_for_state(state)
        signal_path = (
            control_signal_path(state)
            if state.get("report_root") and state.get("run_id")
            else None
        )
        evidence = run_symexec(
            main_root=main_root,
            target_c_file=Path(str(target["c_file"])),
            target_files=target,
            output_root=main_root,
            timeout_seconds=float(profile["timeout_seconds"]),
            profile_name=str(profile["name"]),
            heartbeat_seconds=float(profile["heartbeat_seconds"]),
            poll_interval_seconds=float(profile["poll_interval_seconds"]),
            cancel_requested=(
                (lambda: control_signal_requests_stop(signal_path))
                if signal_path is not None
                else None
            ),
            progress_path=report_directory / progress_name,
        )
    except (OSError, RuntimeError, ValueError) as exc:
        evidence = {
            "status": "failed",
            "returncode": None,
            "first_failure": {
                "category": "tool",
                "kind": "main-root-symexec-invocation",
                "message": str(exc),
                "repair": "Repair the symbolic-execution environment and retry.",
            },
        }
    if evidence.get("status") == "passed":
        try:
            commit_generated_refresh(
                target_files=target,
                report_directory=report_directory,
            )
        except AnnotationRefreshError as exc:
            evidence["status"] = "failed"
            evidence["first_failure"] = exc.failure()
            try:
                rollback_generated_refresh(
                    main_root=main_root,
                    target_files=target,
                    report_directory=report_directory,
                )
            except AnnotationRefreshError as rollback_exc:
                evidence["first_failure"] = rollback_exc.failure()
                refresh_status = "rollback-failed"
            else:
                refresh_status = "rolled-back"
        else:
            refresh_status = "committed"
    else:
        try:
            rollback_generated_refresh(
                main_root=main_root,
                target_files=target,
                report_directory=report_directory,
            )
        except AnnotationRefreshError as exc:
            evidence["first_failure"] = exc.failure()
            refresh_status = "rollback-failed"
        else:
            refresh_status = "rolled-back"
    evidence["generated_refresh"] = {
        **preparation,
        "status": refresh_status,
    }
    return evidence


def _current_matches_annotation_after(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    """Protect receipt reuse and controller generation from post-return drift."""

    relatives = _annotation_snapshot_relatives(state)
    try:
        after = _validated_annotation_attempt_paths(state, attempt)["after"]
        expected = _snapshot_digests(after, relatives)
        current = _snapshot_digests(Path(str(state["main_root"])), relatives)
    except (OSError, ValueError) as exc:
        return [f"annotation post-delivery files cannot be compared: {exc}"]
    return [
        "current main-root file differs from the finalized annotation delivery: "
        + relative
        for relative in relatives
        if expected[relative] != current[relative]
    ]


def _owner_generation_reuse_evidence(
    state: dict[str, Any], attempt: dict[str, Any]
) -> dict[str, Any] | None:
    """Reuse only a controller-written receipt bound to exact sealed bytes."""

    receipt = attempt.get("owner_generation_receipt")
    if not isinstance(receipt, dict) or receipt.get("status") != "passed":
        return None
    if (
        receipt.get("attempt_id") != attempt.get("attempt_id")
        or receipt.get("round") != attempt.get("round")
    ):
        return None
    relatives = _annotation_snapshot_relatives(state)
    try:
        after = _validated_annotation_attempt_paths(state, attempt)["after"]
        after_digests = _snapshot_digests(after, relatives)
    except (OSError, ValueError):
        return None
    if receipt.get("target_digests") != after_digests:
        return None
    main_root = Path(str(state["main_root"]))
    formal_digest = annotation_spec_source_digest(
        main_root / str(state["target_files"]["c_file"]),
        main_root / str(state["target_files"]["formal_case_lib"]),
    )
    if receipt.get("formal_input_digest") != formal_digest:
        return None
    invocations = attempt.get("owner_symexec_invocations")
    if (
        not isinstance(invocations, list)
        or not invocations
        or not isinstance(invocations[-1], dict)
        or invocations[-1].get("status") != "passed"
        or invocations[-1].get("formal_input_digest") != formal_digest
    ):
        return None
    return {
        "status": "passed",
        "returncode": 0,
        "reused_owner_generation": True,
        "owner_generation_receipt": {
            key: receipt.get(key)
            for key in (
                "recorded_at",
                "performance_profile",
                "timeout_seconds",
                "elapsed_seconds",
            )
            if receipt.get(key) is not None
        },
        "generated_refresh": {
            "status": "reused-sealed-owner-generation",
        },
    }


def _annotation_controller_tool_failure(
    *,
    run_root: Path,
    state: dict[str, Any],
    attempt: dict[str, Any],
    stage: str,
    evidence: dict[str, Any],
) -> int | None:
    """Retry one unchanged controller tool in-place, then stop without a new attempt."""

    failure = evidence.get("first_failure")
    if not isinstance(failure, dict) or failure.get("category") not in {
        "tool",
        "tooling",
    }:
        return None
    main_root = Path(str(state["main_root"]))
    formal_digest = annotation_spec_source_digest(
        main_root / str(state["target_files"]["c_file"]),
        main_root / str(state["target_files"]["formal_case_lib"]),
    )
    identity = {
        "stage": stage,
        "kind": str(failure.get("kind") or "unknown-tool-failure"),
        "formal_input_digest": formal_digest,
    }
    records = attempt.setdefault("controller_tool_invocations", [])
    records.append(
        {
            "sequence": len(records) + 1,
            "recorded_at": _utc(),
            **identity,
            "elapsed_seconds": float(
                evidence.get("elapsed_seconds")
                or (evidence.get("symexec") or {}).get("elapsed_seconds")
                or 0.0
            ),
        }
    )
    matching: list[dict[str, Any]] = []
    for item in reversed(records):
        if not isinstance(item, dict) or any(
            item.get(key) != value for key, value in identity.items()
        ):
            break
        matching.append(item)
    matching.reverse()
    attempt["main_check"] = {stage: evidence}
    if len(matching) == 1:
        attempt["status"] = "ready-for-main-check"
        attempt.pop("finished_at", None)
        session = state.get("annotation_session")
        if isinstance(session, dict):
            session["status"] = "awaiting-main-check"
        state["current_blockers"] = []
        state["next_actions"] = [
            {
                "id": f"annotation-check-{attempt['round']}",
                "kind": "main-owned-action",
                "action": "annotation-check-round",
                "round": str(attempt["round"]),
                "attempt_id": str(attempt["attempt_id"]),
            }
        ]
        _append_event(
            run_root,
            state,
            "annotation-controller-tool-retry-same-attempt",
            attempt=attempt["attempt_id"],
            stage=stage,
            kind=identity["kind"],
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "same-attempt-retry-required",
                    "attempt": attempt["attempt_id"],
                    "stage": stage,
                    "failure": failure,
                    "next_actions": hydrate_actions(
                        state, state.get("next_actions", [])
                    ),
                },
                indent=2,
            )
        )
        return 1

    attempt["status"] = "blocked"
    attempt["finished_at"] = _utc()
    _set_annotation_session_idle(state)
    blocker = {
        "failure_class": "tool",
        "kind": "repeated-annotation-controller-tool-blocker",
        "stage": stage,
        "repeated_kind": identity["kind"],
        "formal_input_digest": formal_digest,
        "repeat_count": len(matching),
        "attempts": [str(attempt["attempt_id"])],
        "message": (
            "The same controller-owned annotation acceptance tool failed "
            "twice on unchanged formal input."
        ),
        "repair_boundary": (
            "Repair controller tooling or its performance profile; do not "
            "create another annotation attempt."
        ),
    }
    state["next_actions"] = []
    state["current_blockers"] = [blocker]
    _append_event(
        run_root,
        state,
        "annotation-controller-tool-blocked",
        attempt=attempt["attempt_id"],
        stage=stage,
        kind=identity["kind"],
        repeat_count=len(matching),
    )
    _save_state(run_root, state)
    print(json.dumps({"status": "blocked", "blocker": blocker}, indent=2))
    return 1


def _reject_annotation_precheck(
    *,
    run_root: Path,
    state: dict[str, Any],
    attempt: dict[str, Any],
    reason: str,
    evidence_key: str,
    evidence: Any,
) -> int:
    handled = _annotation_controller_tool_failure(
        run_root=run_root,
        state=state,
        attempt=attempt,
        stage=evidence_key,
        evidence=evidence if isinstance(evidence, dict) else {},
    )
    if handled is not None:
        return handled
    attempt["status"] = "running"
    attempt["main_check"] = {evidence_key: evidence}
    for field in ("returned_at", "finished_at", "artifact_sha256", "after_snapshot"):
        attempt.pop(field, None)
    delivery = attempt.get("delivery")
    if isinstance(delivery, dict):
        delivery.pop("finalized_at", None)
    session = state.get("annotation_session")
    if isinstance(session, dict):
        session["status"] = "running"
    state["current_blockers"] = []
    state["next_actions"] = []
    _append_event(run_root, state, "annotation-check-failed", reason=reason)
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "report-repair-required",
                "attempt": attempt["attempt_id"],
                evidence_key: evidence,
                "message": (
                    "Continue the same annotation attempt with the same owner, "
                    "then rerun finalize-delivery."
                ),
            },
            indent=2,
        )
    )
    return 1


def annotation_check_round(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, "annotation")
    if attempt.get("status") != "ready-for-main-check":
        raise SystemExit("annotation attempt is not ready for main-owned checking")
    try:
        attempt_paths = _validated_annotation_attempt_paths(state, attempt)
        returned_artifact_errors = _artifact_integrity_errors(
            {
                "report": attempt_paths["report"],
                "plan": attempt_paths["plan"],
            },
            attempt.get("artifact_sha256"),
            main_root=main_root,
        )
    except (OSError, ValueError) as exc:
        returned_artifact_errors = [str(exc)]
    if returned_artifact_errors:
        blocker = {
            "failure_class": "annotation-returned-artifact-drift",
            "attempt_id": str(attempt["attempt_id"]),
            "first_error": returned_artifact_errors[0],
            "error_count": len(returned_artifact_errors),
        }
        attempt["status"] = "invalid-report"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {"returned_artifacts": blocker}
        _set_annotation_session_idle(state)
        state["current_blockers"] = [blocker]
        state["next_actions"] = []
        _append_event(
            run_root,
            state,
            "annotation-returned-artifact-drift",
            attempt_id=attempt["attempt_id"],
        )
        _save_state(run_root, state)
        print(json.dumps({"status": "blocked", "blocker": blocker}, indent=2))
        return 1
    after_snapshot_errors = _annotation_after_snapshot_errors(state, attempt)
    if after_snapshot_errors:
        # ``after/`` is controller-owned acceptance provenance.  It cannot be
        # repaired by asking the annotation owner to rewrite its report, so do
        # not leave an impossible retry action queued against corrupted input.
        blocker = {
            "failure_class": "annotation-history-artifact-drift",
            "attempt_id": str(attempt["attempt_id"]),
            "first_error": after_snapshot_errors[0],
            "error_count": len(after_snapshot_errors),
        }
        attempt["status"] = "invalid-report"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {"annotation_history": blocker}
        _set_annotation_session_idle(state)
        state["current_blockers"] = [blocker]
        state["next_actions"] = []
        _append_event(
            run_root,
            state,
            "annotation-history-artifact-drift",
            attempt_id=attempt["attempt_id"],
        )
        _save_state(run_root, state)
        print(json.dumps({"status": "blocked", "blocker": blocker}, indent=2))
        return 1
    current_delivery_errors = _current_matches_annotation_after(state, attempt)
    if current_delivery_errors:
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="post-delivery-current-file-drift",
            evidence_key="current_annotation_delivery",
            evidence={
                "status": "failed",
                "error_count": len(current_delivery_errors),
                "first_error": current_delivery_errors[0],
            },
        )
    target = state["target_files"]

    # The returned plan is bound to the owner's current generated manual before
    # the controller replays symbolic execution.
    try:
        plan = _json_load(annotation_plan_path(state, attempt), {})
        current_vcs = _manual_obligations(state)
        plan_errors = annotation_plan_errors(
            plan,
            c_source=(main_root / target["c_file"]).read_text(encoding="utf-8"),
            failed_vcs=attempt["failed_vcs"],
            current_vcs=current_vcs,
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        plan = None
        plan_errors = [str(exc)]
    if plan_errors:
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="annotation-plan",
            evidence_key="annotation_plan",
            evidence={
                "status": "failed",
                "error_count": len(plan_errors),
                "first_error": plan_errors[0],
            },
        )
    hard_freeze_mismatches = spec_freeze_findings(
        state.get("spec_freeze"),
        c_file=main_root / target["c_file"],
        lib_file=main_root / target["formal_case_lib"],
    )
    if hard_freeze_mismatches:
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="hard-spec-freeze",
            evidence_key="hard_spec_freeze",
            evidence={
                "status": "failed",
                "mismatch_count": len(hard_freeze_mismatches),
                "first_mismatch": hard_freeze_mismatches[0],
            },
        )
    try:
        contract_findings = contract_surface_lint(
            (main_root / target["c_file"]).read_text(encoding="utf-8"),
            (
                (main_root / target["formal_case_lib"]).read_text(
                    encoding="utf-8"
                )
                if (main_root / target["formal_case_lib"]).is_file()
                else ""
            ),
        )
    except (OSError, UnicodeDecodeError) as exc:
        contract_findings = [
            {
                "kind": "contract-surface-lint-input",
                "message": str(exc),
            }
        ]
    if contract_findings:
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="contract-surface-lint",
            evidence_key="contract_surface_lint",
            evidence={
                "status": "failed",
                "finding_count": len(contract_findings),
                "findings": contract_findings,
            },
        )

    # Run the case-lib contract and local Coq check before canonical symexec.
    # The later post-generation check remains an independent acceptance check.
    formal_case_lib_active_pre = _formal_case_lib_is_active(state)
    formal_case_lib_snapshot_pre = _formal_case_lib_snapshot(state)
    formal_case_lib_state_pre = str(
        formal_case_lib_snapshot_pre.get("state") or "invalid"
    )
    if not formal_case_lib_active_pre and formal_case_lib_state_pre != "missing":
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="pre-symexec-absent-formal-case-lib-topology",
            evidence_key="pre_symexec_formal_case_lib_topology",
            evidence={
                "status": "failed",
                "state": formal_case_lib_state_pre,
                "message": str(
                    formal_case_lib_snapshot_pre.get("message")
                    or "absent policy candidate path is no longer missing"
                ),
            },
        )
    if formal_case_lib_active_pre:
        try:
            formal_case_lib_text_pre = _snapshot_text(
                formal_case_lib_snapshot_pre,
                label="formal_case_lib candidate",
            )
            formal_case_lib_errors_pre = lib_contract_errors(
                formal_case_lib_text_pre,
                forbidden_modules=_generated_artifact_module_spellings_for_state(
                    state
                ),
            )
        except (OSError, UnicodeError, ValueError) as exc:
            formal_case_lib_errors_pre = [
                f"formal_case_lib contract could not be evaluated: {exc}"
            ]
        if formal_case_lib_errors_pre:
            return _reject_annotation_precheck(
                run_root=run_root,
                state=state,
                attempt=attempt,
                reason="pre-symexec-formal-case-lib-contract",
                evidence_key="pre_symexec_formal_case_lib_contract",
                evidence={
                    "status": "failed",
                    "errors": formal_case_lib_errors_pre,
                },
            )
        pre_dune = prepare_dune_dependencies(
            workspace_root=main_root,
            target_file=Path(target["formal_case_lib"]),
            current_case_anchor=Path(target["formal_case_lib"]),
        )
        if pre_dune.get("status") != "passed":
            return _reject_annotation_precheck(
                run_root=run_root,
                state=state,
                attempt=attempt,
                reason="pre-symexec-formal-case-lib-dependencies",
                evidence_key="pre_symexec_formal_case_lib_dependencies",
                evidence=_compact_annotation_dune_evidence(pre_dune),
            )
        pre_coqc = run_coqc_check(
            workspace_root=main_root,
            build_workspace=run_builds_root(run_root)
            / args.round
            / "formal-case-lib-pre-symexec"
            / "src",
            target_file=Path(target["formal_case_lib"]),
            target_kind="formal-case-lib-design",
            current_case_anchor=Path(target["formal_case_lib"]),
            dune_preparation=pre_dune,
        )
        if pre_coqc.get("status") != "passed":
            return _reject_annotation_precheck(
                run_root=run_root,
                state=state,
                attempt=attempt,
                reason="pre-symexec-formal-case-lib-coqc",
                evidence_key="pre_symexec_formal_case_lib_coqc",
                evidence={
                    key: pre_coqc.get(key)
                    for key in ("status", "returncode", "first_failure")
                    if pre_coqc.get(key) is not None
                },
            )
    else:
        pre_dune = None
        pre_coqc = {
            "status": "passed",
            "skipped": True,
            "reason": "formal_case_lib policy is absent",
        }

    symexec = _owner_generation_reuse_evidence(state, attempt)
    if symexec is None:
        symexec = _transactional_main_root_symexec(
            state,
            report_directory=attempt_paths["directory"],
        )
    symexec["controller_entrypoint"] = "annotation-check-round"
    if (
        not symexec.get("reused_owner_generation")
        and symexec.get("elapsed_seconds") is not None
    ):
        _record_elapsed_stage(
            attempt,
            "controller-main-refresh",
            float(symexec["elapsed_seconds"]),
        )
        _save_state(run_root, state)
    if symexec.get("status") != "passed":
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="symexec",
            evidence_key="symexec",
            evidence=_compact_symexec_evidence(symexec),
        )
    try:
        obligations = _manual_obligations(state)
    except (OSError, UnicodeError, ValueError) as exc:
        failure = {
            "category": "contract",
            "kind": "generated-manual",
            "relative_path": target["proof_manual_file"],
            "message": str(exc),
            "repair": (
                "Repair the C annotation or any present optional formal_case_lib "
                "input that generated this malformed manual, then rerun canonical "
                "symexec before controller acceptance."
            ),
        }
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="generated-formal-state",
            evidence_key="generated_formal_state",
            evidence={
                "status": "failed",
                "first_failure": failure,
            },
        )
    replayed_plan_errors = annotation_plan_errors(
        plan,
        c_source=(main_root / target["c_file"]).read_text(encoding="utf-8"),
        failed_vcs=attempt["failed_vcs"],
        current_vcs=obligations,
    )
    if replayed_plan_errors:
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="post-symexec-vc-comparison",
            evidence_key="vc_comparisons",
            evidence={
                "status": "failed",
                "error_count": len(replayed_plan_errors),
                "first_error": replayed_plan_errors[0],
            },
        )
    formal_case_lib_active = _formal_case_lib_is_active(state)
    formal_case_lib_snapshot = _formal_case_lib_snapshot(state)
    formal_case_lib_state = str(formal_case_lib_snapshot.get("state") or "invalid")
    if not formal_case_lib_active and formal_case_lib_state == "missing":
        formal_case_lib_contract = {
            "status": "passed",
            "skipped": True,
            "reason": "optional formal_case_lib candidate is absent",
        }
        formal_case_lib_errors: list[str] = []
    elif not formal_case_lib_active:
        inactive_path_error = (
            "formal_case_lib is absent from the fixed run topology but the "
            "read-only candidate path is not truly absent"
        )
        if formal_case_lib_snapshot.get("message"):
            inactive_path_error += f": {formal_case_lib_snapshot['message']}"
        formal_case_lib_errors = [inactive_path_error]
        formal_case_lib_contract = {
            "status": "failed",
            "skipped": False,
            "errors": formal_case_lib_errors,
        }
    elif formal_case_lib_state != "present":
        invalid_path_error = (
            "formal_case_lib candidate is not a readable non-link regular file: "
            f"{target['formal_case_lib']}"
        )
        if formal_case_lib_snapshot.get("message"):
            invalid_path_error += f": {formal_case_lib_snapshot['message']}"
        formal_case_lib_errors = [invalid_path_error]
        formal_case_lib_contract = {
            "status": "failed",
            "skipped": False,
            "errors": formal_case_lib_errors,
        }
    else:
        try:
            formal_case_lib_text = _snapshot_text(
                formal_case_lib_snapshot,
                label="formal_case_lib candidate",
            )
            formal_case_lib_errors = lib_contract_errors(
                formal_case_lib_text,
                forbidden_modules=_generated_artifact_module_spellings_for_state(
                    state,
                ),
            )
        except (OSError, UnicodeError, ValueError) as exc:
            formal_case_lib_errors = [
                f"formal_case_lib contract could not be evaluated: {exc}"
            ]
        formal_case_lib_contract = {
            "status": "failed" if formal_case_lib_errors else "passed",
            "skipped": False,
            "errors": formal_case_lib_errors,
        }
    if formal_case_lib_errors:
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="formal-case-lib-contract",
            evidence_key="formal_case_lib_contract",
            evidence=formal_case_lib_contract,
        )
    dune_preparation: dict[str, Any] | None = None
    if formal_case_lib_active:
        # The selected backend resolves and prepares the exact library target
        # before local coqc. This receipt is intentionally ephemeral:
        # acceptance performs a fresh goal-check preparation and seals it.
        dune_preparation = prepare_dune_dependencies(
            workspace_root=main_root,
            target_file=Path(target["formal_case_lib"]),
            current_case_anchor=Path(target["proof_auto_file"]),
        )
        if dune_preparation.get("status") != "passed":
            return _reject_annotation_precheck(
                run_root=run_root,
                state=state,
                attempt=attempt,
                reason="formal-case-lib-dune",
                evidence_key="formal_case_lib_dune",
                evidence=dune_preparation,
            )
    if not formal_case_lib_active:
        formal_case_lib_check = {
            "status": "passed",
            "skipped": True,
            "reason": "optional formal_case_lib candidate is absent",
            "target_file": str(target["formal_case_lib"]),
            "returncode": None,
        }
    else:
        formal_case_lib_check = run_coqc_check(
            workspace_root=main_root,
            build_workspace=run_builds_root(run_root)
            / args.round
            / "formal-case-lib"
            / "src",
            target_file=Path(target["formal_case_lib"]),
            target_kind="formal-case-lib",
            current_case_anchor=Path(target["proof_auto_file"]),
            dune_preparation=dune_preparation,
        )
    formal_case_lib_check["controller_entrypoint"] = "annotation-check-round"
    if formal_case_lib_check.get("elapsed_seconds") is not None:
        _record_elapsed_stage(
            attempt,
            "formal-case-lib-coq-check",
            float(formal_case_lib_check["elapsed_seconds"]),
        )
    if formal_case_lib_check.get("status") != "passed":
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="formal-case-lib-coqc",
            evidence_key="formal_case_lib_coqc",
            evidence=formal_case_lib_check,
        )
    profile = symexec_profile_for_state(state)
    signal_path = control_signal_path(state)
    freshness = clean_output_freshness(
        main_root=main_root,
        target_c_file=Path(target["c_file"]),
        target_files=target,
        reference_root=main_root,
        refresh_root=Path(str(attempt["report_directory"])) / "clean-output-freshness",
        manual_mode="raw",
        symexec_runner=run_symexec,
        timeout_seconds=float(profile["timeout_seconds"]),
        profile_name=str(profile["name"]),
        heartbeat_seconds=float(profile["heartbeat_seconds"]),
        cancel_requested=lambda: control_signal_requests_stop(signal_path),
        progress_path=attempt_paths["directory"]
        / "symexec-progress-clean-replay.json",
    )
    freshness["controller_entrypoint"] = "annotation-check-round"
    freshness_elapsed = freshness.get("symexec", {}).get("elapsed_seconds")
    if freshness_elapsed is not None:
        _record_elapsed_stage(
            attempt,
            "clean-replay",
            float(freshness_elapsed),
        )
    if freshness.get("status") != "passed":
        freshness_tool_evidence = freshness.get("symexec")
        handled = _annotation_controller_tool_failure(
            run_root=run_root,
            state=state,
            attempt=attempt,
            stage="clean-replay",
            evidence=(
                freshness_tool_evidence
                if isinstance(freshness_tool_evidence, dict)
                else {}
            ),
        )
        if handled is not None:
            return handled
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="clean-output-freshness",
            evidence_key="clean_output_freshness",
            evidence={
                key: freshness.get(key)
                for key in (
                    "status",
                    "symexec",
                    "mismatches",
                    "interrupted_output_recovery",
                )
            },
        )
    final_vcs = _manual_obligations(state)
    final_comparison_errors = annotation_plan_errors(
        plan,
        c_source=(main_root / target["c_file"]).read_text(encoding="utf-8"),
        failed_vcs=attempt["failed_vcs"],
        current_vcs=final_vcs,
    )
    if final_comparison_errors:
        return _reject_annotation_precheck(
            run_root=run_root,
            state=state,
            attempt=attempt,
            reason="clean-replay-vc-comparison",
            evidence_key="vc_comparisons",
            evidence={
                "status": "failed",
                "error_count": len(final_comparison_errors),
                "first_error": final_comparison_errors[0],
            },
        )
    _update_user_spec_baseline(state, main_root=main_root)
    attempt["status"] = "accepted"
    attempt["finished_at"] = _utc()
    comparisons = plan["vc_comparisons"]
    attempt["main_check"] = {
        "vc_comparisons": {
            "status": "passed",
            "comparison_count": len(comparisons),
            "resolved_count": sum(
                comparison["result"] == "resolved"
                for comparison in comparisons
            ),
            "statements": [
                {
                    "source": dict(comparison["source"]),
                    "current": list(comparison["current"]),
                }
                for comparison in comparisons
            ],
        },
        "pre_symexec_formal_case_lib_coqc": {
            key: pre_coqc.get(key)
            for key in ("status", "skipped", "reason", "returncode")
            if pre_coqc.get(key) is not None
        },
        "symexec": _compact_symexec_evidence(symexec),
        "formal_case_lib_contract": formal_case_lib_contract,
        **(
            {
                "formal_case_lib_dune": _compact_annotation_dune_evidence(
                    dune_preparation
                )
            }
            if dune_preparation is not None
            else {}
        ),
        "formal_case_lib_coqc": {
            key: formal_case_lib_check.get(key)
            for key in ("status", "skipped", "reason", "returncode")
            if formal_case_lib_check.get(key) is not None
        },
        "clean_output_freshness": {
            key: freshness.get(key)
            for key in ("status", "interrupted_output_recovery")
        },
    }
    state["accepted_rounds"]["annotation"] = {
        "round": args.round,
        "attempt_id": attempt["attempt_id"],
        "annotation_history_directory": attempt["annotation_history_directory"],
    }
    # The earlier case-lib build was an annotation check.  Only the exact
    # post-acceptance goal-check build may become the proving dependency seal.
    state["dune_preparation"] = None
    _set_annotation_session_idle(state)
    state["phase"] = "annotation"
    state["next_actions"] = []
    _append_event(
        run_root,
        state,
        "annotation-round-accepted",
        round=args.round,
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "accepted",
                "target_witness_count": len(final_vcs["top_level"]),
                "comparison_count": len(comparisons),
            },
            indent=2,
        )
    )
    return 0


def _verify_group_plan(state: dict[str, Any], plan_path: Path) -> dict[str, Any]:
    plan = _json_load(plan_path, {})
    if not isinstance(plan, dict):
        raise SystemExit("group plan must be a JSON object")
    obligations = _manual_obligations(state)
    if set(plan) != {"groups"}:
        raise SystemExit("group plan must contain only groups")

    entries = group_entries_from_plan(obligations, plan)
    if not _formal_case_lib_is_active(state) and any(
        entry["planned_helpers"] for entry in entries
    ):
        raise SystemExit(
            "group plan cannot declare helpers without formal_case_lib"
        )
    canonical_groups: list[dict[str, Any]] = []
    for entry in entries:
        group_id = str(entry["group_id"])
        if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", group_id) is None:
            raise SystemExit(f"proof group id is not path-safe: {group_id}")
        if len(entry["witnesses"]) > int(state["max_witnesses_per_group"]):
            raise SystemExit(f"proof group {group_id} exceeds max_witnesses_per_group")
        canonical_witnesses = [
            {
                "name": str(witness["name"]),
                "proof_mode": str(witness["proof_mode"]),
                **(
                    {"strategy": str(witness["strategy"])}
                    if witness.get("proof_mode") == "LLM_pre_process"
                    else {}
                ),
                "split_goals": [
                    {
                        "name": str(split_goal["name"]),
                        **(
                            {"strategy": str(split_goal["strategy"])}
                            if split_goal.get("strategy")
                            else {}
                        ),
                    }
                    for split_goal in witness["split_goals"]
                ],
            }
            for witness in entry["witnesses"]
        ]
        canonical: dict[str, Any] = {
            "id": group_id,
            "estimated_difficulty": entry["estimated_difficulty"],
            "witnesses": canonical_witnesses,
        }
        if entry["planned_helpers"]:
            canonical["helpers"] = [
                {
                    "name": str(helper["name"]),
                    "strategy": str(helper["strategy"]),
                    "visibility": str(helper["visibility"]),
                }
                for helper in entry["planned_helpers"]
            ]
        canonical_groups.append(canonical)
    return {"groups": canonical_groups}


def _vc_checking_candidate_preflight_errors(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    """Check the owner-authored group plan before sealing the delivery."""

    if _current_files_errors(state):
        return []
    structural_errors = _vc_structural_scan_errors(
        state,
        attempt,
        expected_status="passed",
    )
    if structural_errors:
        return structural_errors
    try:
        report_directory = fixed_path_under(
            Path(str(attempt["report_directory"])),
            Path(str(state["report_root"])),
            label="vc-checking report directory",
        )
        _verify_group_plan(state, report_directory / "group_plan.json")
    except (OSError, TypeError, UnicodeError, ValueError, SystemExit) as exc:
        return [str(exc)]
    return []



def _vc_agent_output_metrics(path: Path) -> dict[str, int | str]:
    try:
        raw = path.read_bytes()
        text = raw.decode("utf-8")
    except (OSError, UnicodeDecodeError):
        return {
            "bytes": 0,
            "lines": 0,
            "common_pattern_count": 0,
            "vc_delta_count": 0,
            "structural_scan_present": 0,
            "structural_top_level_scanned": 0,
            "structural_no_split_checked_first": 0,
            "structural_definite_blockers": 0,
        }
    structural_match = re.search(
        r"^## Structural Blocker Scan\s*$\n(.*?)(?=^## |\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    structural_body = structural_match.group(1) if structural_match else ""

    def structural_integer(label: str) -> int:
        match = re.search(
            rf"^- {re.escape(label)}:\s*(\d+)\s*$",
            structural_body,
            flags=re.MULTILINE,
        )
        return int(match.group(1)) if match is not None else 0

    structural_status = re.search(
        r"^- Status:\s*(passed|blocked|pending)\s*$",
        structural_body,
        flags=re.MULTILINE,
    )
    common_match = re.search(
        r"^## Common Proof Patterns\s*$\n(.*?)(?=^## |\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    common_pattern_count = (
        len(
            re.findall(
                r"^###\s+\S",
                common_match.group(1),
                flags=re.MULTILINE,
            )
        )
        if common_match is not None
        else 0
    )
    delta_match = re.search(
        r"^## VC Deltas\s*$\n(.*?)(?=^## |\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    vc_delta_count = 0
    if delta_match is not None:
        for line in delta_match.group(1).splitlines():
            stripped = line.strip()
            if (
                not stripped.startswith("|")
                or stripped.lower().startswith("| vc |")
                or re.fullmatch(r"\|[\s:|-]+\|", stripped)
            ):
                continue
            vc_delta_count += 1
    return {
        "bytes": len(raw),
        "lines": len(text.splitlines()),
        "common_pattern_count": common_pattern_count,
        "vc_delta_count": vc_delta_count,
        "structural_scan_present": int(structural_match is not None),
        "structural_status": (
            structural_status.group(1) if structural_status is not None else ""
        ),
        "structural_top_level_scanned": structural_integer(
            "Top-level VCs scanned"
        ),
        "structural_no_split_checked_first": structural_integer(
            "No-split VCs checked first"
        ),
        "structural_definite_blockers": structural_integer(
            "Definite blockers"
        ),
    }


def _vc_structural_scan_errors(
    state: dict[str, Any],
    attempt: dict[str, Any],
    *,
    expected_status: str,
) -> list[str]:
    """Enforce the cheap top-level scan before expensive split analysis."""

    metrics = _vc_agent_output_metrics(Path(str(attempt["output"])))
    try:
        obligations = _manual_obligations(state)
    except (OSError, UnicodeError, ValueError) as exc:
        return [f"current manual cannot be counted for structural scan: {exc}"]
    witness_count = len(obligations["top_level"])
    no_split_count = sum(
        not obligations["split_goals"].get(str(witness))
        for witness in obligations["top_level"]
    )
    errors: list[str] = []
    if not metrics["structural_scan_present"]:
        return ["agent_output.md is missing the Structural Blocker Scan section"]
    if metrics.get("structural_status") != expected_status:
        errors.append(
            "Structural Blocker Scan status must be " + expected_status
        )
    scanned = int(metrics["structural_top_level_scanned"])
    checked_first = int(metrics["structural_no_split_checked_first"])
    blockers = int(metrics["structural_definite_blockers"])
    if expected_status == "passed":
        if scanned != witness_count:
            errors.append(
                "Structural Blocker Scan must cover every top-level VC: "
                f"expected {witness_count}, recorded {scanned}"
            )
        if checked_first != no_split_count:
            errors.append(
                "Structural Blocker Scan must check every no-split VC first: "
                f"expected {no_split_count}, recorded {checked_first}"
            )
        if blockers != 0:
            errors.append(
                "a completed VC plan cannot retain a definite structural blocker"
            )
    else:
        if scanned < 1 or scanned > witness_count:
            errors.append(
                "a blocked structural scan must record a non-empty bounded "
                "top-level scan count"
            )
        if checked_first < 0 or checked_first > no_split_count:
            errors.append("blocked structural no-split count is out of range")
        if blockers < 1:
            errors.append("a blocked structural scan must record a definite blocker")
    return errors


def vc_checking_check_round(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt = _attempt_for_round(state, args.round, "vc-checking")
    if attempt.get("status") != "ready-for-main-check":
        raise SystemExit("vc-checking attempt is not ready for main-owned checking")
    file_errors = _current_files_errors(state)
    if file_errors:
        _transition_current_file_drift(
            state,
            attempt,
            action="vc-checking-check-round",
            feedback_attempt_id=str(attempt["attempt_id"]),
        )
        _append_event(
            run_root,
            state,
            "vc-checking-file-drift",
            round=args.round,
            first_error=file_errors[0],
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "stale",
                    "errors": file_errors,
                    "next_actions": hydrate_actions(
                        state, state.get("next_actions", [])
                    ),
                },
                indent=2,
            )
        )
        return 1

    report_directory = fixed_path_under(
        Path(str(attempt["report_directory"])),
        Path(str(state["report_root"])),
        label="vc-checking report directory",
    )
    expected_plan_path = fixed_path_under(
        report_directory / "group_plan.json",
        report_directory,
        label="vc-checking group plan",
    )
    supplied_plan_path = (
        Path(args.group_plan).expanduser() if args.group_plan else expected_plan_path
    )
    plan_path = fixed_path_under(
        supplied_plan_path,
        report_directory,
        label="vc-checking group plan",
    )
    if plan_path != expected_plan_path:
        raise SystemExit(
            f"group_plan.json must use the current round report path: {expected_plan_path}"
        )

    agent_output_metrics = _vc_agent_output_metrics(Path(str(attempt["output"])))
    attempt["agent_output_metrics"] = agent_output_metrics
    refresh: dict[str, Any] | None = None
    clean_manual_sha256: str | None = None
    try:
        owner_manual_signature = _current_manual_vc_signature(state)
        plan = _verify_group_plan(state, plan_path)
        refresh = _transactional_main_root_symexec(
            state,
            report_directory=report_directory,
            progress_name="symexec-progress-post-vc-checking.json",
        )
        if refresh.get("elapsed_seconds") is not None:
            _record_elapsed_stage(
                attempt,
                "post-vc-checking-symexec",
                float(refresh["elapsed_seconds"]),
            )
        if refresh.get("status") != "passed":
            failure = refresh.get("first_failure")
            raise RuntimeError(
                str(
                    failure.get("message")
                    if isinstance(failure, dict)
                    else "symbolic execution failed while restoring the clean manual"
                )
            )
        clean_manual_signature = _current_manual_vc_signature(state)
        if clean_manual_signature != owner_manual_signature:
            raise ValueError(
                "vc-checking proof manual differs from clean output after "
                "removing temporary Show commands"
            )
        clean_manual_sha256 = _proof_manual_sha256(state)
        clean_plan = _verify_group_plan(state, plan_path)
        if clean_plan != plan:
            raise ValueError(
                "group plan changed meaning after the clean manual was regenerated"
            )
        if _proof_manual_sha256(state) != clean_manual_sha256:
            raise ValueError(
                "clean proof manual changed while the group plan was revalidated"
            )
        file_errors = _current_files_errors(state)
        if file_errors:
            raise ValueError(file_errors[0])
    except (OSError, TypeError, UnicodeError, ValueError, RuntimeError, SystemExit) as exc:
        first_error = str(exc)
        refresh_failed = refresh is not None and refresh.get("status") != "passed"
        blocker = {
            "failure_class": "vc-manual-refresh" if refresh_failed else "vc-plan",
            "first_error": first_error,
        }
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
            "group_plan": {"status": "failed", "first_error": first_error},
            **(
                {"manual_refresh": _compact_symexec_evidence(refresh)}
                if refresh is not None
                else {}
            ),
        }
        state["current_blockers"] = [blocker]
        if refresh_failed:
            _queue_annotation_feedback(
                state,
                str(attempt["attempt_id"]),
                "vc-checking-manual-refresh-failed",
            )
        else:
            _queue_vc_checking_retry(
                state,
                attempt,
                "vc-checking-invalid-report",
            )
        _append_event(
            run_root,
            state,
            "vc-checking-main-check-failed",
            round=args.round,
            first_error=first_error,
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "failed",
                    "blocker": blocker,
                    "next_actions": hydrate_actions(
                        state, state.get("next_actions", [])
                    ),
                },
                indent=2,
            )
        )
        return 1

    plan_sha256 = _file_digest(plan_path)
    attempt["status"] = "accepted"
    attempt["finished_at"] = _utc()
    attempt["group_plan"] = str(plan_path)
    attempt["group_plan_sha256"] = plan_sha256
    attempt["main_check"] = {
        "manual_refresh": _compact_symexec_evidence(refresh or {})
    }
    state["accepted_rounds"]["vc-checking"] = {
        "round": args.round,
        "attempt_id": attempt["attempt_id"],
        "group_plan": str(plan_path),
        "group_plan_sha256": plan_sha256,
        "proof_manual_sha256": clean_manual_sha256,
        "agent_output_metrics": agent_output_metrics,
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
                "manual_refreshed": True,
                "agent_output_metrics": agent_output_metrics,
            },
            indent=2,
        )
    )
    return 0
