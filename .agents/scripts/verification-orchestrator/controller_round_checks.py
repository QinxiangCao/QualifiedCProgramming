#!/usr/bin/env python3
"""Main-owned checks that accept annotation and vc-checking rounds.

This module is internal to controller.py.  It replays required tooling,
validates a round against current formal state, and records acceptance.
"""

from __future__ import annotations

import argparse
import json
import os
import re
from collections import Counter
from pathlib import Path
from typing import Any

from controller_attempts import (
    _attempt_for_round,
    _proving_manifest_errors,
    _queue_annotation_feedback,
    _queue_vc_checking_retry,
    _transition_current_version_drift,
)
from controller_invocations import hydrate_actions
from spec_freeze import spec_freeze_findings
from controller_rounds import (
    _latest_reusable_vc_proving_round,
    _reusable_group_ids,
    _sealed_reuse_raw_artifacts,
    _stable_fixed_file_snapshot,
    _validated_reuse_raw_root,
)
from controller_state import (
    _annotation_after_snapshot_errors,
    _append_event,
    _current_version_errors,
    _debug_build_snapshot,
    _file_digest,
    _formal_case_lib_is_active,
    _formal_case_lib_snapshot,
    _generated_artifact_module_spellings_for_state,
    _json_load,
    _load_state,
    _record_elapsed_stage,
    _run_root_from_id,
    _save_state,
    _source_goal_version,
    _source_version_for_state,
    _utc,
    _verified_reuse_source_build,
)
from coq_tooling import (
    dune_snapshot_for_preserved_build,
    prepare_dune_dependencies,
    run_coqc_check,
)
from file_integrity import sha256_bytes
from group_plan_utils import (
    PROOF_MODES,
    group_entries_from_plan,
)
from path_utils import (
    fixed_path_under,
    reuse_source_build_workspace,
    run_builds_root,
    vc_checking_build_workspace,
    vc_checking_debug_script,
)
from prepare_group_workers import (
    resolve_group_workers_manifest,
)
from proof_manual_utils import (
    block_has_incomplete_proof,
    debug_goal_show_contract,
    goal_definition_hashes,
    goal_semantic_hash_for_lemma,
    is_exact_declaration_line_range,
    lemma_by_name,
    lemma_statement_hash,
    lemma_target_symbol,
    lib_contract_errors,
    markdown_table_cells,
    normalize_reuse_decision,
    parse_manual_file,
    proof_mode_errors,
    show_command_count,
)
from symexec_tooling import _snapshot_text, clean_output_freshness, run_symexec
from verify_group_results import validate_group_for_acceptance_result


def _set_annotation_session_idle(state: dict[str, Any]) -> None:
    session = state.get("annotation_session")
    if isinstance(session, dict):
        session["status"] = "idle"


def _compact_symexec_evidence(symexec: dict[str, Any]) -> dict[str, Any]:
    return {
        key: symexec.get(key)
        for key in ("status", "returncode", "first_failure")
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
    target = state["target_files"]
    symexec = run_symexec(
        main_root=main_root,
        target_c_file=Path(target["c_file"]),
        target_files=target,
        output_root=main_root,
    )
    symexec["controller_entrypoint"] = "annotation-check-round"
    if symexec.get("elapsed_seconds") is not None:
        _record_elapsed_stage(attempt, "symexec", float(symexec["elapsed_seconds"]))
        _save_state(run_root, state)
    if symexec.get("status") != "passed":
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {"symexec": _compact_symexec_evidence(symexec)}
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(
            state, attempt["attempt_id"], "annotation-main-check-symexec"
        )
        _append_event(run_root, state, "annotation-check-failed", reason="symexec")
        _save_state(run_root, state)
        print(json.dumps({"status": "failed", "symexec": symexec}, indent=2))
        return 1
    try:
        source_goal = _source_goal_version(state)
    except (OSError, ValueError) as exc:
        failure = {
            "category": "contract",
            "kind": "source-goal-version",
            "relative_path": target["proof_manual_file"],
            "message": str(exc),
            "repair": (
                "Repair the C annotation or any present optional formal_case_lib "
                "input that generated this malformed manual, then rerun canonical "
                "symexec before controller acceptance."
            ),
        }
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
            "symexec": _compact_symexec_evidence(symexec),
            "generated_formal_state": {
                "status": "failed",
                "first_failure": failure,
            },
        }
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(
            state,
            attempt["attempt_id"],
            "annotation-main-check-generated-formal-state",
        )
        _append_event(
            run_root,
            state,
            "annotation-check-failed",
            reason="generated-formal-state",
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {"status": "failed", "generated_formal_state": failure},
                indent=2,
            )
        )
        return 1
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
                    source_goal_version=source_goal,
                ),
            )
        except (UnicodeError, ValueError) as exc:
            formal_case_lib_errors = [
                f"formal_case_lib contract could not be evaluated: {exc}"
            ]
        formal_case_lib_contract = {
            "status": "failed" if formal_case_lib_errors else "passed",
            "skipped": False,
            "errors": formal_case_lib_errors,
        }
    if formal_case_lib_errors:
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
            "symexec": _compact_symexec_evidence(symexec),
            "formal_case_lib_contract": formal_case_lib_contract,
        }
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(
            state,
            attempt["attempt_id"],
            "annotation-main-check-formal-case-lib-contract",
        )
        _append_event(
            run_root,
            state,
            "annotation-check-failed",
            reason="formal-case-lib-contract",
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "failed",
                    "formal_case_lib_contract": formal_case_lib_errors,
                },
                indent=2,
            )
        )
        return 1
    # A run may fix part of the specification surface as input.  The agent owns
    # the whole C file and case lib, so this is the only place the boundary is
    # enforced: compare the frozen entries against the run's baseline.
    spec_freeze_mismatches = spec_freeze_findings(
        state.get("spec_freeze"),
        c_file=main_root / target["c_file"],
        lib_file=main_root / target["formal_case_lib"],
    )
    if spec_freeze_mismatches:
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
            "symexec": _compact_symexec_evidence(symexec),
            "spec_freeze": {
                "status": "failed",
                "mismatch_count": len(spec_freeze_mismatches),
                "first_mismatch": spec_freeze_mismatches[0],
            },
        }
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(
            state,
            attempt["attempt_id"],
            "annotation-main-check-spec-freeze",
        )
        _append_event(
            run_root,
            state,
            "annotation-check-failed",
            reason="spec-freeze",
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {"status": "failed", "spec_freeze": spec_freeze_mismatches},
                indent=2,
            )
        )
        return 1
    source_version = _source_version_for_state(state, annotated=True)
    dune_preparation: dict[str, Any] | None = None
    if formal_case_lib_active:
        # The selected backend resolves and prepares the exact library target
        # before local coqc. This receipt is intentionally ephemeral:
        # acceptance performs a fresh goal-check preparation and seals it.
        dune_preparation = prepare_dune_dependencies(
            workspace_root=main_root,
            target_file=Path(target["formal_case_lib"]),
            current_case_anchor=Path(target["proof_auto_file"]),
            source_goal_version=str(source_version["digest"]),
        )
        if dune_preparation.get("status") != "passed":
            blocker = dune_preparation.get("first_failure")
            if not isinstance(blocker, dict):
                makefile_mode = dune_preparation.get("build_mode") == "makefile"
                blocker = {
                    "category": "tooling",
                    "kind": (
                        "makefile-build-failed"
                        if makefile_mode
                        else "dune-build-failed"
                    ),
                    "message": (
                        "Makefile preparation failed before the formal-case-lib check."
                        if makefile_mode
                        else "Dune failed before the formal-case-lib check."
                    ),
                    "repair": (
                        "Repair the first Make/coqdep/Rocq diagnostic and rerun the same check."
                        if makefile_mode
                        else "Repair the first Dune/Rocq diagnostic and rerun the same check."
                    ),
                }
            attempt["status"] = "main-check-failed"
            attempt["finished_at"] = _utc()
            attempt["main_check"] = {
                "symexec": _compact_symexec_evidence(symexec),
                "formal_case_lib_dune": _compact_annotation_dune_evidence(
                    dune_preparation
                ),
            }
            _set_annotation_session_idle(state)
            _queue_annotation_feedback(
                state,
                attempt["attempt_id"],
                "annotation-main-check-formal-case-lib-dune",
            )
            _append_event(
                run_root,
                state,
                "annotation-check-failed",
                reason="formal-case-lib-dune",
            )
            _save_state(run_root, state)
            print(
                json.dumps(
                    {"status": "failed", "formal_case_lib_dune": dune_preparation},
                    indent=2,
                )
            )
            return 1
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
            source_goal_version=source_version["digest"],
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
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
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
                for key in (
                    "status",
                    "skipped",
                    "reason",
                    "returncode",
                    "first_failure",
                )
                if formal_case_lib_check.get(key) is not None
            },
        }
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(
            state, attempt["attempt_id"], "annotation-main-check-formal-case-lib-coqc"
        )
        _append_event(
            run_root, state, "annotation-check-failed", reason="formal-case-lib-coqc"
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {"status": "failed", "formal_case_lib_coqc": formal_case_lib_check},
                indent=2,
            )
        )
        return 1
    freshness = clean_output_freshness(
        main_root=main_root,
        target_c_file=Path(target["c_file"]),
        target_files=target,
        reference_root=main_root,
        refresh_root=Path(str(attempt["report_directory"])) / "clean-output-freshness",
        manual_mode="raw",
        symexec_runner=run_symexec,
    )
    freshness["controller_entrypoint"] = "annotation-check-round"
    freshness_elapsed = freshness.get("symexec", {}).get("elapsed_seconds")
    if freshness_elapsed is not None:
        _record_elapsed_stage(
            attempt,
            "clean-output-freshness",
            float(freshness_elapsed),
        )
    if (
        freshness.get("status") != "passed"
        or freshness.get("source_goal_version", {}).get("reference")
        != source_goal["digest"]
    ):
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
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
                for key in ("status", "symexec", "mismatches", "source_goal_version")
            },
        }
        _set_annotation_session_idle(state)
        _queue_annotation_feedback(
            state,
            attempt["attempt_id"],
            "annotation-main-check-clean-output-freshness",
        )
        _append_event(
            run_root,
            state,
            "annotation-check-failed",
            reason="clean-output-freshness",
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {"status": "failed", "clean_output_freshness": freshness},
                indent=2,
            )
        )
        return 1
    state["source_version"] = source_version
    state["source_goal_version"] = source_goal
    attempt["status"] = "accepted"
    attempt["finished_at"] = _utc()
    attempt["main_check"] = {
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
            key: freshness.get(key) for key in ("status", "source_goal_version")
        },
    }
    state["accepted_rounds"]["annotation"] = {
        "round": args.round,
        "attempt_id": attempt["attempt_id"],
        "annotation_history_directory": attempt["annotation_history_directory"],
        "source_version": source_version["digest"],
        "source_goal_version": source_goal["digest"],
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
    targets = [str(item) for item in state["source_goal_version"]["target_witnesses"]]
    if set(plan) != {"groups"}:
        raise SystemExit("group plan must contain only groups")

    synthetic_lemmas = [
        {"name": declaration}
        for witness in targets
        for declaration in [
            *[
                str(item["name"])
                for item in state["source_goal_version"]
                .get("split_goals", {})
                .get(witness, [])
            ],
            witness,
        ]
    ]
    entries = group_entries_from_plan(synthetic_lemmas, plan)
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


REUSE_HINT_COLUMNS = (
    "current goal",
    "decision",
    "previous file",
    "lines",
    "reason",
)
REUSE_DECISIONS = {"direct copy", "partial proof-idea reuse", "from scratch"}
EMPTY_REUSE_REFERENCE = {"—"}


def _sealed_group_artifact_digest(
    proving: dict[str, Any], group: dict[str, Any], artifact: str
) -> str:
    group_id = str(group["id"])
    reuse_record = proving.get("reuse_group_artifacts")
    reuse_groups = (
        reuse_record.get("groups") if isinstance(reuse_record, dict) else None
    )
    if isinstance(reuse_groups, dict):
        group_record = reuse_groups.get(group_id)
        if isinstance(group_record, dict) and group_record.get(artifact):
            return str(group_record[artifact])
    accepted = (
        proving.get("groups", {}).get(group_id, {}).get("accepted_artifact_sha256")
    )
    if isinstance(accepted, dict) and accepted.get(artifact):
        return str(accepted[artifact])
    raise SystemExit(f"proof reuse source `{group_id}` has no sealed {artifact} digest")


def _read_sealed_utf8(
    path: Path,
    expected_sha256: str,
    label: str,
    *,
    owner: Path,
) -> str:
    try:
        snapshot = _stable_fixed_file_snapshot(path, owner=owner, label=label)
    except (OSError, ValueError) as exc:
        raise SystemExit(f"sealed {label} cannot be read: {path}: {exc}") from exc
    if snapshot.get("sha256") != expected_sha256:
        raise SystemExit(f"sealed {label} changed before proof reuse: {path}")
    try:
        return _snapshot_text(snapshot, label=label)
    except ValueError as exc:
        raise SystemExit(f"sealed {label} is not UTF-8: {path}: {exc}") from exc


def _qualified_goal_target(state: dict[str, Any], target_symbol: str) -> str:
    target = state["target_files"]
    return f"{target['active_case_theory']}.{target['case_name']}_goal.{target_symbol}"


def _reuse_hint_rows(path: Path, *, text: str | None = None) -> list[dict[str, str]]:
    table_lines = [
        line.strip()
        for line in (
            text if text is not None else path.read_text(encoding="utf-8")
        ).splitlines()
        if line.strip().startswith("|") and line.strip().endswith("|")
    ]
    rows = [markdown_table_cells(line) for line in table_lines]
    header_index = next(
        (
            index
            for index, row in enumerate(rows)
            if tuple(cell.lower() for cell in row) == REUSE_HINT_COLUMNS
        ),
        None,
    )
    if header_index is None or header_index + 1 >= len(rows):
        raise SystemExit(f"reuse hint must contain the five-column table in {path}")
    separator = rows[header_index + 1]
    if len(separator) != len(REUSE_HINT_COLUMNS) or not all(
        re.fullmatch(r":?-{3,}:?", cell) for cell in separator
    ):
        raise SystemExit(f"reuse hint table separator is invalid in {path}")
    result: list[dict[str, str]] = []
    for row in rows[header_index + 2 :]:
        if len(row) != len(REUSE_HINT_COLUMNS):
            raise SystemExit(f"reuse hint table row must have five columns in {path}")
        result.append(dict(zip(REUSE_HINT_COLUMNS, row, strict=True)))
    if not result:
        raise SystemExit(f"reuse hint table has no goal rows in {path}")
    return result


def _previous_reuse_ranges(
    state: dict[str, Any], source_round: str
) -> dict[str, list[dict[str, Any]]]:
    if _latest_reusable_vc_proving_round(state) != source_round:
        raise SystemExit(
            "proof reuse source must still be the immediately preceding sealed reusable vc-proving round"
        )
    proving = state.get("attempts", {}).get(source_round)
    if not isinstance(proving, dict):
        raise SystemExit("proof reuse source attempt is missing")
    integrity_errors = _proving_manifest_errors(state, proving)
    if integrity_errors:
        raise SystemExit(
            "proof reuse source manifest failed integrity: "
            + "; ".join(integrity_errors)
        )
    try:
        reuse_source_root = _validated_reuse_raw_root(state, proving)
    except (OSError, TypeError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    manifest = resolve_group_workers_manifest(
        Path(str(proving["group_workers_manifest"])),
        main_root=Path(str(state["main_root"])),
        seed_root=reuse_source_root,
        expected_run_root=Path(str(state["run_root"])),
        expected_round=str(proving["round"]),
    )
    if not isinstance(manifest, dict):
        raise SystemExit("proof reuse source manifest is invalid")
    ranges: dict[str, list[dict[str, Any]]] = {
        **{mode: [] for mode in PROOF_MODES},
        "helper": [],
    }
    try:
        raw_artifacts = _sealed_reuse_raw_artifacts(state, proving)
    except (OSError, TypeError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    if raw_artifacts["proof_manual_file"]["sha256"] is None:
        if manifest.get("groups"):
            raise SystemExit(
                "proof reuse source has groups despite a null raw proof manual"
            )
        return ranges
    has_formal_case_lib = raw_artifacts["formal_case_lib"]["sha256"] is not None
    try:
        reference_goal_hashes = goal_definition_hashes(
            bytes(raw_artifacts["goal_file"]["data"]).decode("utf-8"),
            formal_case_lib_text=(
                bytes(raw_artifacts["formal_case_lib"]["data"]).decode("utf-8")
                if has_formal_case_lib
                else ""
            ),
        )
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        raise SystemExit(
            f"sealed previous generated goal file cannot be hashed: {exc}"
        ) from exc
    reusable_group_ids = _reusable_group_ids(proving, manifest)
    for group in manifest.get("groups", []):
        if not isinstance(group, dict):
            continue
        group_id = str(group.get("id") or "")
        if group_id not in reusable_group_ids:
            continue
        group_was_controller_checked = (
            proving.get("groups", {}).get(group_id, {}).get("status") == "accepted"
        )
        try:
            source_validation = validate_group_for_acceptance_result(
                Path(str(proving["group_workers_manifest"])),
                group_id=group_id,
                main_root=Path(str(state["main_root"])),
                expected_proof_manual=str(state["target_files"]["proof_manual_file"]),
                expected_formal_case_lib=str(state["target_files"]["formal_case_lib"]),
                require_complete=False,
                seed_root=reuse_source_root,
                expected_run_root=Path(str(state["run_root"])),
                expected_round=str(proving["round"]),
                forbidden_modules=_generated_artifact_module_spellings_for_state(
                    state,
                    source_goal_version=state["source_goal_version"],
                ),
            )
        except (OSError, UnicodeDecodeError, ValueError, SystemExit) as exc:
            raise SystemExit(
                f"previous group source cannot be structurally validated: {group_id}: {exc}"
            ) from exc
        source_errors = [str(item) for item in source_validation.get("errors", [])]
        if source_errors:
            raise SystemExit(
                "previous group source changed outside its assigned proof spans: "
                + source_errors[0]
            )
        group_directory = Path(str(group.get("directory") or ""))
        manual = Path(str(group.get("proof_manual") or ""))
        manual_sha256 = _sealed_group_artifact_digest(proving, group, "proof_manual")
        try:
            _prelude, lemmas = parse_manual_file(
                _read_sealed_utf8(
                    manual,
                    manual_sha256,
                    "group proof manual",
                    owner=group_directory,
                )
            )
        except (OSError, ValueError) as exc:
            raise SystemExit(
                f"previous group manual cannot be parsed: {manual}: {exc}"
            ) from exc
        by_name = lemma_by_name(lemmas)
        for witness in group.get("witnesses", []):
            if not isinstance(witness, dict):
                continue
            mode = str(witness.get("proof_mode") or "")
            if mode not in PROOF_MODES:
                raise SystemExit(
                    "previous group manifest contains an invalid proof mode"
                )
            split_names = [
                str(split_goal.get("name") or "")
                for split_goal in witness.get("split_goals", [])
                if isinstance(split_goal, dict)
            ]
            if mode == "aggressive_pre_process":
                names = split_names
            else:
                names = [str(witness.get("name") or "")]
            for name in names:
                lemma = by_name.get(name)
                if not isinstance(lemma, dict):
                    raise SystemExit(
                        f"previous {mode} proof block is missing from {manual}: {name}"
                    )
                target_symbol = lemma_target_symbol(lemma)
                if target_symbol is None:
                    raise SystemExit(
                        f"previous proof block has no simple generated goal target: {name}"
                    )
                route_complete = (
                    not proof_mode_errors(str(lemma["block"]), mode)
                    if mode == "LLM_pre_process"
                    else True
                )
                ranges[mode].append(
                    {
                        "name": name,
                        "target_symbol": _qualified_goal_target(state, target_symbol),
                        "path": manual,
                        "start": int(lemma["start_line"]),
                        "end": int(lemma["end_line"]),
                        "complete": not block_has_incomplete_proof(str(lemma["block"]))
                        and route_complete
                        and group_was_controller_checked,
                        "controller_checked": group_was_controller_checked,
                        "statement_hash": lemma_statement_hash(lemma),
                        "goal_definition_hash": goal_semantic_hash_for_lemma(
                            lemma, reference_goal_hashes
                        ),
                        "source_sha256": manual_sha256,
                    }
                )
        if not has_formal_case_lib:
            if group.get("group_worker_lib") or group.get("helpers"):
                raise SystemExit(
                    "no-lib proof reuse group contains helper/library topology"
                )
            continue
        raw_worker_lib = group.get("group_worker_lib")
        if not isinstance(raw_worker_lib, str) or not raw_worker_lib:
            raise SystemExit(
                "present-lib proof reuse group lacks group_worker_lib"
            )
    return ranges


def _current_generated_artifact_state(
    state: dict[str, Any], role: str
) -> str:
    source_goal = state.get("source_goal_version")
    records = source_goal.get("generated_files") if isinstance(source_goal, dict) else None
    matches = (
        [
            record
            for record in records
            if isinstance(record, dict) and record.get("role") == role
        ]
        if isinstance(records, list)
        else []
    )
    if len(matches) != 1:
        raise SystemExit(
            f"current source_goal_version requires exactly one {role} record"
        )
    record = matches[0]
    artifact_state = record.get("state")
    digest = record.get("sha256")
    if (
        record.get("relative_path") != state["target_files"][role]
        or artifact_state not in {"present", "missing"}
        or (artifact_state == "missing" and digest is not None)
        or (
            artifact_state == "present"
            and (
                not isinstance(digest, str)
                or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            )
        )
    ):
        raise SystemExit(
            f"current source_goal_version has an invalid {role} record"
        )
    return str(artifact_state)


def _expected_reuse_rows(group: dict[str, Any]) -> dict[str, dict[str, str]]:
    """Return one group's reuse units in the required category order.

    The reuse contract is helpers, every aggressive split goal, then every
    LLM whole goal.  Relative order within each category remains the order in
    the candidate plan (and, for splits, the raw-manual declaration order).
    """

    expected_rows: dict[str, dict[str, str]] = {
        f"helper:{helper['name']}": {
            "mode": "helper",
            "kind": "helper",
            "helper_name": str(helper["name"]),
        }
        for helper in group.get("helpers", [])
        if isinstance(helper, dict)
    }
    for witness in group["witnesses"]:
        if witness["proof_mode"] != "aggressive_pre_process":
            continue
        expected_rows.update(
            {
                str(split_goal["name"]): {
                    "mode": "aggressive_pre_process",
                    "kind": "proof",
                }
                for split_goal in witness["split_goals"]
            }
        )
    for witness in group["witnesses"]:
        if witness["proof_mode"] != "LLM_pre_process":
            continue
        expected_rows[str(witness["name"])] = {
            "mode": "LLM_pre_process",
            "kind": "proof",
        }
    return expected_rows


def _plan_reuse_rows(group: dict[str, Any]) -> dict[str, dict[str, str]]:
    """Expand reuse units by traversing the candidate plan as written."""

    plan_rows: dict[str, dict[str, str]] = {
        f"helper:{helper['name']}": {
            "mode": "helper",
            "kind": "helper",
            "helper_name": str(helper["name"]),
        }
        for helper in group.get("helpers", [])
        if isinstance(helper, dict)
    }
    for witness in group["witnesses"]:
        name = str(witness["name"])
        mode = str(witness["proof_mode"])
        if mode == "aggressive_pre_process":
            plan_rows.update(
                {
                    str(split_goal["name"]): {
                        "mode": mode,
                        "kind": "proof",
                    }
                    for split_goal in witness["split_goals"]
                }
            )
        elif mode == "LLM_pre_process":
            plan_rows[name] = {"mode": mode, "kind": "proof"}
    return plan_rows


def _reuse_order_error(
    *,
    group_id: str,
    plan_path: Path,
    hint_path: Path,
    plan_names: list[str],
    required_names: list[str],
    actual_names: list[str],
) -> str:
    """Render a three-sequence, machine-readable reuse-order mismatch."""

    plan_mismatch = plan_names != required_names
    hint_mismatch = actual_names != required_names
    primary_names = plan_names if plan_mismatch else actual_names

    mismatch_index = next(
        (
            index
            for index, (expected, actual) in enumerate(
                zip(required_names, primary_names, strict=False)
            )
            if expected != actual
        ),
        min(len(required_names), len(primary_names)),
    )
    plan_mismatch_index = (
        next(
            (
                index
                for index, (required, planned) in enumerate(
                    zip(required_names, plan_names, strict=False)
                )
                if required != planned
            ),
            min(len(required_names), len(plan_names)),
        )
        if plan_mismatch
        else None
    )
    hint_mismatch_index = (
        next(
            (
                index
                for index, (required, actual) in enumerate(
                    zip(required_names, actual_names, strict=False)
                )
                if required != actual
            ),
            min(len(required_names), len(actual_names)),
        )
        if hint_mismatch
        else None
    )
    mismatching_sequences = [
        sequence
        for sequence, mismatches in (
            ("expected_from_plan", plan_mismatch),
            ("actual_hint", hint_mismatch),
        )
        if mismatches
    ]
    detail = {
        "code": (
            "vc-reuse-plan-category-order"
            if plan_mismatch
            else "vc-reuse-hint-row-order"
        ),
        "artifact": "group_plan" if plan_mismatch else "reuse_hint",
        "group_id": group_id,
        "path": str(plan_path if plan_mismatch else hint_path),
        "group_plan_path": str(plan_path),
        "hint_path": str(hint_path),
        "required_categories": [
            "helpers",
            "aggressive_pre_process split goals",
            "LLM_pre_process top-level VCs",
        ],
        "mismatching_sequences": mismatching_sequences,
        "first_mismatch_row": mismatch_index + 1,
        "plan_first_mismatch_row": (
            plan_mismatch_index + 1 if plan_mismatch_index is not None else None
        ),
        "hint_first_mismatch_row": (
            hint_mismatch_index + 1 if hint_mismatch_index is not None else None
        ),
        "expected_at_mismatch": (
            required_names[mismatch_index]
            if mismatch_index < len(required_names)
            else None
        ),
        "actual_at_mismatch": (
            primary_names[mismatch_index]
            if mismatch_index < len(primary_names)
            else None
        ),
        "plan_count": len(plan_names),
        "required_count": len(required_names),
        "hint_count": len(actual_names),
        "expected_from_plan": plan_names,
        "required_category_order": required_names,
        "actual_hint": actual_names,
        "repair": (
            (
                "reorder both mixed-mode group_plan witnesses and reuse-hint "
                "rows to the required category order; preserve relative "
                "order within each category"
            )
            if plan_mismatch and hint_mismatch
            else (
                "reorder mixed-mode group_plan witnesses so all "
                "aggressive_pre_process witnesses precede all "
                "LLM_pre_process witnesses while preserving relative order "
                "within each segment"
                if plan_mismatch
                else "reorder reuse-hint rows to the required category order"
            )
        ),
    }
    return "reuse comparison sequence mismatch: " + json.dumps(
        detail,
        ensure_ascii=False,
        sort_keys=True,
    )


def _reuse_order_error_for(
    *,
    group_id: str,
    plan_path: Path,
    hint_path: Path,
    group: dict[str, Any],
    actual_names: list[str],
) -> str | None:
    """Require plan traversal, category order, and hint rows to be identical."""

    plan_names = list(_plan_reuse_rows(group))
    required_names = list(_expected_reuse_rows(group))
    if plan_names == required_names == actual_names:
        return None
    return _reuse_order_error(
        group_id=group_id,
        plan_path=plan_path,
        hint_path=hint_path,
        plan_names=plan_names,
        required_names=required_names,
        actual_names=actual_names,
    )


def _vc_checking_candidate_preflight_errors(
    state: dict[str, Any], attempt: dict[str, Any]
) -> list[str]:
    """Check owner-repairable VC plan/hint layout before delivery sealing.

    The main-owned round check remains the acceptance authority and performs
    semantic reuse/source/debug validation.  This preflight intentionally
    covers only candidate-local plan shape, hint file coverage, table shape,
    and the exact row sequence so a mechanical output defect can be repaired
    by the same owner in the same attempt.
    """

    if _current_version_errors(state):
        # Post-seal validation gives source drift precedence over owner output
        # defects and transitions the attempt through the existing stale path.
        return []
    try:
        report_directory = fixed_path_under(
            Path(str(attempt["report_directory"])),
            Path(str(state["report_root"])),
            label="vc-checking report directory",
        )
        plan_path = fixed_path_under(
            report_directory / "group_plan.json",
            report_directory,
            label="vc-checking group plan",
        )
        plan = _verify_group_plan(state, plan_path)
        hint_root = fixed_path_under(
            report_directory / "reuse_hints",
            report_directory,
            label="vc-checking reuse-hint directory",
        )
        actual_files: set[Path] = set()
        if hint_root.is_dir():
            for candidate in hint_root.rglob("*"):
                fixed_candidate = fixed_path_under(
                    candidate,
                    hint_root,
                    label="vc-checking reuse-hint artifact",
                )
                if fixed_candidate.is_file():
                    actual_files.add(fixed_candidate)
        if not str(attempt.get("proof_reuse_round") or ""):
            if actual_files:
                raise SystemExit(
                    "reuse-hint files are forbidden without an immediately "
                    "preceding sealed reusable vc-proving round"
                )
            return []
        expected_paths = {
            str(group["id"]): fixed_path_under(
                hint_root / f"{group['id']}.md",
                hint_root,
                label="vc-checking reuse-hint file",
            )
            for group in plan["groups"]
        }
        if actual_files != set(expected_paths.values()):
            missing = sorted(
                str(path)
                for path in set(expected_paths.values()) - actual_files
            )
            extra = sorted(
                str(path)
                for path in actual_files - set(expected_paths.values())
            )
            raise SystemExit(
                "reuse-hint files must match proof groups exactly; "
                f"missing={missing}; extra={extra}"
            )
        for group in plan["groups"]:
            group_id = str(group["id"])
            path = expected_paths[group_id]
            try:
                hint_text = path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as exc:
                raise SystemExit(
                    f"reuse hint cannot be read: {path}: {exc}"
                ) from exc
            rows = _reuse_hint_rows(path, text=hint_text)
            actual_names = [row["current goal"] for row in rows]
            order_error = _reuse_order_error_for(
                group_id=group_id,
                plan_path=plan_path,
                hint_path=path,
                group=group,
                actual_names=actual_names,
            )
            if order_error is not None:
                raise SystemExit(order_error)
    except (OSError, TypeError, UnicodeError, ValueError, SystemExit) as exc:
        return [str(exc)]
    return []


def _verify_reuse_hints(
    state: dict[str, Any], attempt: dict[str, Any], plan: dict[str, Any]
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, str],
    dict[str, str],
]:
    report_directory = fixed_path_under(
        Path(str(attempt["report_directory"])),
        Path(str(state["report_root"])),
        label="vc-checking report directory",
    )
    hint_root = fixed_path_under(
        report_directory / "reuse_hints",
        report_directory,
        label="vc-checking reuse-hint directory",
    )
    source_round = str(attempt.get("proof_reuse_round") or "")
    actual_files: set[Path] = set()
    if hint_root.is_dir():
        for candidate in hint_root.rglob("*"):
            fixed_candidate = fixed_path_under(
                candidate,
                hint_root,
                label="vc-checking reuse-hint artifact",
            )
            if fixed_candidate.is_file():
                actual_files.add(fixed_candidate)
    current_manual = Path(str(state["main_root"])) / str(
        state["target_files"]["proof_manual_file"]
    )
    current_manual_state = _current_generated_artifact_state(
        state,
        "proof_manual_file",
    )
    if current_manual_state == "missing":
        if os.path.lexists(current_manual):
            raise SystemExit(
                "current proof manual is sealed missing but its path exists"
            )
        if source_round or plan.get("groups") or actual_files:
            raise SystemExit(
                "proof reuse is forbidden when the current proof manual is absent"
            )
        return {}, {}, {}
    if not source_round:
        if actual_files:
            raise SystemExit(
                "reuse-hint files are forbidden without an immediately preceding sealed reusable vc-proving round"
            )
        return {}, {}, {}
    previous_ranges = _previous_reuse_ranges(state, source_round)
    try:
        _prelude, current_lemmas = parse_manual_file(
            current_manual.read_text(encoding="utf-8")
        )
    except (OSError, ValueError) as exc:
        raise SystemExit(
            f"current raw manual cannot be inspected for reuse: {exc}"
        ) from exc
    current_by_name = lemma_by_name(current_lemmas)
    current_goal = Path(str(state["main_root"])) / str(
        state["target_files"]["goal_file"]
    )
    current_formal_case_lib = Path(str(state["main_root"])) / str(
        state["target_files"]["formal_case_lib"]
    )
    try:
        if _formal_case_lib_is_active(state):
            current_formal_case_lib_text = current_formal_case_lib.read_text(
                encoding="utf-8"
            )
        elif os.path.lexists(current_formal_case_lib):
            raise ValueError(
                "formal_case_lib is sealed missing but its path exists"
            )
        else:
            current_formal_case_lib_text = ""
        current_goal_hashes = goal_definition_hashes(
            current_goal.read_text(encoding="utf-8"),
            formal_case_lib_text=current_formal_case_lib_text,
        )
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        raise SystemExit(
            f"current generated goal file cannot be hashed: {exc}"
        ) from exc
    expected_paths = {
        str(group["id"]): fixed_path_under(
            hint_root / f"{group['id']}.md",
            hint_root,
            label="vc-checking reuse-hint file",
        )
        for group in plan["groups"]
    }
    if actual_files != set(expected_paths.values()):
        missing = sorted(
            str(path) for path in set(expected_paths.values()) - actual_files
        )
        extra = sorted(
            str(path) for path in actual_files - set(expected_paths.values())
        )
        raise SystemExit(
            f"reuse-hint files must match proof groups exactly; missing={missing}; extra={extra}"
        )
    result: dict[str, dict[str, Any]] = {}
    current_debug_goals: dict[str, str] = {}
    reference_debug_goals: dict[str, str] = {}
    for group in plan["groups"]:
        group_id = str(group["id"])
        path = expected_paths[group_id]
        try:
            hint_bytes = path.read_bytes()
            hint_text = hint_bytes.decode("utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            raise SystemExit(f"reuse hint cannot be read: {path}: {exc}") from exc
        expected_rows = _expected_reuse_rows(group)
        for name in expected_rows:
            if expected_rows[name]["kind"] == "helper":
                continue
            lemma = current_by_name.get(name)
            target_symbol = lemma_target_symbol(lemma) if lemma is not None else None
            if target_symbol is None:
                raise SystemExit(
                    f"current proof block has no simple generated goal target: {name}"
                )
            current_debug_goals[name] = _qualified_goal_target(state, target_symbol)
            expected_rows[name]["statement_hash"] = lemma_statement_hash(lemma)
            expected_rows[name]["goal_definition_hash"] = goal_semantic_hash_for_lemma(
                lemma, current_goal_hashes
            )
        rows = _reuse_hint_rows(path, text=hint_text)
        referenced_sources: dict[Path, str] = {}
        actual_names = [row["current goal"] for row in rows]
        order_error = _reuse_order_error_for(
            group_id=group_id,
            plan_path=report_directory / "group_plan.json",
            hint_path=path,
            group=group,
            actual_names=actual_names,
        )
        if order_error is not None:
            raise SystemExit(order_error)
        for row in rows:
            name = row["current goal"]
            expected = expected_rows[name]
            decision = normalize_reuse_decision(row["decision"])
            previous_file = row["previous file"]
            lines = row["lines"]
            reason = row["reason"].strip()
            if decision not in REUSE_DECISIONS:
                raise SystemExit(f"reuse hint has an invalid decision for {name}")
            if not reason:
                raise SystemExit(f"reuse hint requires a reason for {name}")
            empty_file = previous_file.lower() in EMPTY_REUSE_REFERENCE
            empty_lines = lines.lower() in EMPTY_REUSE_REFERENCE
            if expected["kind"] == "helper" and decision != "from scratch":
                raise SystemExit(
                    f"helper reuse must be from scratch: {name}"
                )
            if decision == "from scratch":
                if not empty_file or not empty_lines:
                    raise SystemExit(
                        f"from-scratch reuse hint must omit previous file and lines: {name}"
                    )
                continue
            if empty_file or empty_lines:
                raise SystemExit(
                    f"reused goal requires a previous file and exact line range: {name}"
                )
            previous_path = Path(previous_file).expanduser()
            normalized_previous_path = Path(
                os.path.abspath(os.fspath(previous_path))
            )
            if (
                not previous_path.is_absolute()
                or previous_path != normalized_previous_path
            ):
                raise SystemExit(f"reuse hint previous file must be absolute: {name}")
            previous_path = normalized_previous_path
            line_match = re.fullmatch(r"(\d+)(?:\s*-\s*(\d+))?", lines)
            if line_match is None:
                raise SystemExit(f"reuse hint has an invalid line range for {name}")
            start = int(line_match.group(1))
            end = int(line_match.group(2) or start)
            if start < 1 or end < start:
                raise SystemExit(f"reuse hint has an invalid line range for {name}")
            compatible = next(
                (
                    item
                    for item in previous_ranges[expected["mode"]]
                    if item["path"] == previous_path
                    and is_exact_declaration_line_range(
                        start,
                        end,
                        declaration_start=int(item["start"]),
                        declaration_end=int(item["end"]),
                    )
                    and (
                        expected["kind"] != "helper"
                        or str(item["name"]) == str(expected["helper_name"])
                    )
                ),
                None,
            )
            if compatible is None:
                raise SystemExit(
                    f"reuse hint does not reference a compatible previous {expected['mode']} proof block: {name}"
                )
            if decision == "direct copy" and not compatible["complete"]:
                raise SystemExit(
                    f"direct-copy reuse source is not a completed previous proof: {name}"
                )
            if (
                expected["kind"] == "proof"
                and decision == "direct copy"
                and compatible.get("goal_definition_hash")
                != expected.get("goal_definition_hash")
            ):
                raise SystemExit(
                    "direct-copy reuse requires an exact current/previous generated-goal "
                    f"definition hash: {name}"
                )
            source_sha256 = str(compatible.get("source_sha256") or "")
            if not source_sha256:
                raise SystemExit(f"reused goal has no sealed source digest: {name}")
            previous_digest = referenced_sources.get(previous_path)
            if previous_digest is not None and previous_digest != source_sha256:
                raise SystemExit(
                    f"reused source has conflicting sealed digests: {previous_path}"
                )
            referenced_sources[previous_path] = source_sha256
            if expected["kind"] != "helper":
                reference_debug_goals[str(compatible["name"])] = str(
                    compatible["target_symbol"]
                )
        result[group_id] = {
            "path": str(path),
            "sha256": sha256_bytes(hint_bytes),
            "sources": [
                {"path": str(source), "sha256": referenced_sources[source]}
                for source in sorted(referenced_sources)
            ],
        }
    return result, current_debug_goals, reference_debug_goals


def _debug_script_acceptance_errors(
    *,
    label: str,
    path: Path,
    receipt: dict[str, Any],
    goals: dict[str, str],
) -> list[str]:
    if not path.is_file():
        return [f"{label} debug script is missing"]
    errors: list[str] = []
    debug_files = {item.resolve() for item in path.parent.rglob("*") if item.is_file()}
    if debug_files != {path.resolve()}:
        errors.append(f"{label} debug directory must contain only its declared script")
    if receipt.get("debug_script_sha256") != _file_digest(path):
        errors.append(f"{label} debug script changed after coq-debug")
    script_text = path.read_text(encoding="utf-8")
    script_errors, shown_targets = debug_goal_show_contract(script_text)
    errors.extend(f"{label} debug script: {error}" for error in script_errors)
    if receipt.get("show_count") != show_command_count(script_text):
        errors.append(f"{label} debug Show count changed after coq-debug")
    required_goal_count = len(goals)
    if len(shown_targets) < required_goal_count:
        errors.append(
            f"{label} debug script must use a separate `Goal ... Show.` block for every compared goal"
        )
    required_targets = list(goals.values())
    for name, target_symbol in goals.items():
        if shown_targets.count(target_symbol) < required_targets.count(target_symbol):
            errors.append(
                f"{label} debug script does not Show goal `{name}` ({target_symbol})"
            )
    if Counter(shown_targets) != Counter(required_targets):
        errors.append(
            f"{label} debug script Shows an unlisted or duplicate goal target"
        )
    return errors


def _verify_reuse_debug_evidence(
    state: dict[str, Any],
    attempt: dict[str, Any],
    current_goals: dict[str, str],
    reference_goals: dict[str, str],
) -> None:
    source_round = str(attempt.get("proof_reuse_round") or "")
    proving = state.get("attempts", {}).get(source_round)
    if not source_round or not isinstance(proving, dict):
        raise SystemExit("proof reuse debug source round is missing")
    receipts = attempt.get("proof_reuse_debug")
    if not isinstance(receipts, dict):
        raise SystemExit(
            "proof reuse requires successful current and previous coq-debug commands"
        )
    run_root = Path(str(state["run_root"]))
    current_goal_version = str(state["source_goal_version"]["digest"])
    reference_goal_version = str(proving.get("source_goal_version") or "")
    sealed_reference = proving.get("reuse_source_snapshot")
    if not isinstance(sealed_reference, dict):
        raise SystemExit("previous vc-proving round lacks a sealed reuse-source build")
    specifications = [
        (
            "current",
            str(attempt["round"]),
            current_goal_version,
            vc_checking_build_workspace(run_root, str(attempt["round"])),
            vc_checking_debug_script(
                run_root, str(attempt["round"])
            ).relative_to(
                vc_checking_build_workspace(run_root, str(attempt["round"]))
            ),
            current_goals,
        )
    ]
    if reference_goals:
        specifications.append(
            (
                "reference",
                source_round,
                reference_goal_version,
                reuse_source_build_workspace(run_root, source_round),
                Path(".coq_debug/reuse-source.v"),
                reference_goals,
            )
        )
    errors: list[str] = []
    for (
        label,
        round_id,
        goal_version,
        build_workspace,
        script_rel,
        goals,
    ) in specifications:
        receipt = receipts.get(label)
        if not isinstance(receipt, dict) or receipt.get("status") != "passed":
            errors.append(f"{label} coq-debug has no passed controller receipt")
            continue
        try:
            if label == "reference":
                _dependency_snapshot, snapshot = _verified_reuse_source_build(
                    main_root=Path(str(state["main_root"])),
                    run_root=run_root,
                    round_id=round_id,
                    sealed=sealed_reference,
                    source_goal_version=goal_version,
                )
            else:
                snapshot = _debug_build_snapshot(
                    build_workspace,
                    dune_dependency_snapshot=dune_snapshot_for_preserved_build(
                        workspace_root=Path(str(state["main_root"])),
                        receipt=state.get("dune_preparation"),
                    ),
                )
        except (OSError, ValueError) as exc:
            errors.append(str(exc))
            continue
        if receipt.get("round") != round_id:
            errors.append(f"{label} coq-debug round is stale")
        if receipt.get("source_goal_version") != goal_version:
            errors.append(f"{label} coq-debug source_goal_version is stale")
        if (
            receipt.get("build_digest") != snapshot["digest"]
            or receipt.get("build_file_count") != snapshot["file_count"]
        ):
            errors.append(f"{label} debug build changed after coq-debug")
        errors.extend(
            _debug_script_acceptance_errors(
                label=label,
                path=build_workspace / script_rel,
                receipt=receipt,
                goals=goals,
            )
        )
    if errors:
        raise SystemExit("proof reuse debug evidence failed: " + "; ".join(errors))


def _vc_agent_output_metrics(path: Path) -> dict[str, int]:
    try:
        raw = path.read_bytes()
        text = raw.decode("utf-8")
    except (OSError, UnicodeDecodeError):
        return {
            "bytes": 0,
            "lines": 0,
            "common_pattern_count": 0,
            "vc_delta_count": 0,
        }
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
    }


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
    version_errors = _current_version_errors(state)
    if version_errors:
        _transition_current_version_drift(
            state,
            attempt,
            action="vc-checking-check-round",
            feedback_attempt_id=str(attempt["attempt_id"]),
        )
        _append_event(
            run_root,
            state,
            "vc-checking-version-drift",
            round=args.round,
            first_error=version_errors[0],
        )
        _save_state(run_root, state)
        print(
            json.dumps(
                {
                    "status": "stale",
                    "errors": version_errors,
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
    agent_output_metrics = _vc_agent_output_metrics(
        Path(str(attempt["output"]))
    )
    attempt["agent_output_metrics"] = agent_output_metrics
    try:
        plan = _verify_group_plan(state, plan_path)
        reuse_hints, current_debug_goals, reference_debug_goals = _verify_reuse_hints(
            state, attempt, plan
        )
        if reuse_hints:
            _verify_reuse_debug_evidence(
                state,
                attempt,
                current_debug_goals,
                reference_debug_goals,
            )
    except (OSError, TypeError, UnicodeError, ValueError, SystemExit) as exc:
        # The owner delivery is already sealed and main owns this check.  A
        # bare exception would leave the same check action queued against bytes
        # that only the finished vc-checking agent was authorized to create.
        # Use the existing same-phase retry so a fresh no-parent-transcript
        # agent receives this controller evidence in its handoff.
        first_error = str(exc)
        blocker = {
            "failure_class": "vc-plan",
            "first_error": first_error,
        }
        attempt["status"] = "main-check-failed"
        attempt["finished_at"] = _utc()
        attempt["main_check"] = {
            "group_plan": {"status": "failed", "first_error": first_error}
        }
        state["current_blockers"] = [blocker]
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
    state["accepted_rounds"]["vc-checking"] = {
        "round": args.round,
        "attempt_id": attempt["attempt_id"],
        "group_plan": str(plan_path),
        "group_plan_sha256": plan_sha256,
        "agent_output_metrics": agent_output_metrics,
    }
    if reuse_hints:
        state["accepted_rounds"]["vc-checking"].update(
            {
                "proof_reuse_round": str(attempt["proof_reuse_round"]),
                "reuse_hints": reuse_hints,
            }
        )
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
                "agent_output_metrics": agent_output_metrics,
            },
            indent=2,
        )
    )
    return 0
