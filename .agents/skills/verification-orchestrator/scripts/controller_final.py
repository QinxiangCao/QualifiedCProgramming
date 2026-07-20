#!/usr/bin/env python3
"""Apply the accepted proving_merged candidate and perform final checks.

This module is internal to controller.py and is the only implementation that
copies an accepted proof candidate back to the formal main-root paths.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
from pathlib import Path
from typing import Any

from coq_tooling import run_coqc_check
from path_utils import run_builds_root
from proof_manual_utils import (
    ASSUMPTION_DECLARATION_KINDS,
    PROOF_DECLARATION_KINDS,
    forbidden_top_level_declarations,
    incomplete_proof_markers,
    lemma_statement_hash,
    parse_manual_file,
    rollback_control_commands,
    strip_coq_comments,
    top_level_commands,
    unsafe_assumption_declarations,
    unsafe_typing_commands,
    write_split_manual_artifacts,
)
from verify_group_results import FORBIDDEN_LEMMAS
from symexec_tooling import run_symexec

from controller_state import (
    _append_event,
    _file_digest,
    _is_relative_to,
    _json_load,
    _load_state,
    _run_root_from_id,
    _save_state,
    _utc,
)
from controller_rounds import VC_PROVING_PHASE


def _candidate_target_errors(state: dict[str, Any], candidate: dict[str, Any]) -> list[str]:
    target = state["target_files"]
    errors: list[str] = []
    if candidate.get("formal_proof_manual_relative") != target["proof_manual_file"]:
        errors.append("final candidate manual destination does not match current target")
    if candidate.get("formal_case_lib_relative") != target["formal_case_lib"]:
        errors.append("final candidate lib destination does not match current target")
    return errors


def _backup_file(source: Path, main_root: Path, backup_root: Path) -> dict[str, Any]:
    relative = source.relative_to(main_root)
    backup = backup_root / relative
    record = {
        "target": str(source),
        "relative_path": relative.as_posix(),
        "existed": source.is_file(),
        "backup": str(backup),
    }
    if source.is_file():
        backup.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, backup)
        record["sha256"] = _file_digest(source)
    return record


def _rollback(records: list[dict[str, Any]]) -> dict[str, Any]:
    restored: list[str] = []
    errors: list[str] = []
    for record in records:
        target = Path(str(record["target"]))
        try:
            if record.get("existed"):
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(Path(str(record["backup"])), target)
            elif target.exists():
                target.unlink()
            restored.append(str(target))
        except OSError as exc:
            errors.append(f"{target}: {exc}")
    return {
        "status": "passed" if not errors else "failed",
        "restored": restored,
        "errors": errors,
    }


def final_apply(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    if state.get("phase") != "final-candidate-apply":
        raise SystemExit("final-apply requires the final-candidate-apply controller phase")
    candidate = state.get("final_candidate")
    if not isinstance(candidate, dict):
        raise SystemExit("final candidate is missing")
    target_errors = _candidate_target_errors(state, candidate)
    if target_errors:
        raise SystemExit("; ".join(target_errors))
    source_manual = Path(str(candidate["proof_manual"])).resolve()
    source_lib = Path(str(candidate["proving_merged_lib"])).resolve()
    accepted = state.get("accepted_rounds", {}).get(VC_PROVING_PHASE, {})
    current_goal = str(state.get("source_goal_version", {}).get("digest") or "")
    accepted_goal = str(accepted.get("source_goal_version") or "")
    candidate_goal = str(candidate.get("source_goal_version") or "")
    if not current_goal or accepted_goal != current_goal or candidate_goal != current_goal:
        raise SystemExit("final candidate source_goal_version is stale")
    merge_result_path = Path(str(candidate.get("proving_merged_result", ""))).resolve()
    merge_result = _json_load(merge_result_path, {})
    merged = merge_result if isinstance(merge_result, dict) else None
    merged_candidate = merged.get("candidate") if isinstance(merged, dict) else None
    if (
        not isinstance(merged, dict)
        or merged.get("schema_version") != "qcp-vc-proving-proving-merged-result/v2"
        or merged.get("status") != "passed"
        or merged.get("source_goal_version") != current_goal
        or not isinstance(merged_candidate, dict)
    ):
        raise SystemExit("final candidate lacks an accepted proving_merged_result")
    if Path(str(merged_candidate.get("proof_manual", ""))).resolve() != source_manual:
        raise SystemExit("final manual does not match proving_merged_result")
    if Path(str(merged_candidate.get("proving_merged_lib", ""))).resolve() != source_lib:
        raise SystemExit("final lib does not match proving_merged_result")
    if candidate.get("proof_manual_sha256") != merged_candidate.get("proof_manual_sha256"):
        raise SystemExit("final manual digest is not pinned to proving_merged_result")
    if candidate.get("proving_merged_lib_sha256") != merged_candidate.get("proving_merged_lib_sha256"):
        raise SystemExit("final lib digest is not pinned to proving_merged_result")
    if not source_manual.is_file() or not source_lib.is_file():
        raise SystemExit("final candidate files are missing")
    if merged_candidate.get("proof_manual_sha256") != _file_digest(source_manual):
        raise SystemExit("final manual digest does not match proving_merged_result")
    if merged_candidate.get("proving_merged_lib_sha256") != _file_digest(source_lib):
        raise SystemExit("final lib digest does not match proving_merged_result")
    accepted_directory = Path(str(accepted.get("directory", ""))).resolve()
    if not _is_relative_to(source_manual, accepted_directory / "proving_merged") or not _is_relative_to(source_lib, accepted_directory / "proving_merged"):
        raise SystemExit("final candidate is outside accepted proving_merged directory")
    targets = [
        (source_manual, main_root / str(candidate["formal_proof_manual_relative"])),
        (source_lib, main_root / str(candidate["formal_case_lib_relative"])),
    ]
    backup_root = Path(str(state["report_root"])) / "final-check" / "backup"
    records = [_backup_file(target, main_root, backup_root) for _source, target in targets]
    copied: list[dict[str, Any]] = []
    try:
        for source, target in targets:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
            copied.append(
                {
                    "source": str(source),
                    "target": str(target),
                    "sha256": _file_digest(target),
                }
            )
    except OSError as exc:
        rollback = _rollback(records)
        state["final_apply"] = {
            "status": "failed",
            "error": str(exc),
            "backup": records,
            "rollback": rollback,
        }
        _append_event(run_root, state, "final-apply-failed", error=str(exc))
        _save_state(run_root, state)
        return 1
    state["final_apply"] = {
        "status": "passed",
        "backup": records,
        "copied_files": copied,
        "applied_at": _utc(),
    }
    state["phase"] = "final-check"
    state["next_actions"] = [{"id": "final-check", "kind": "main-owned-action", "action": "final-check"}]
    applied_relatives = [str(candidate["formal_proof_manual_relative"]), str(candidate["formal_case_lib_relative"])]
    _append_event(run_root, state, "final-candidate-applied", files=applied_relatives)
    _save_state(run_root, state)
    print(json.dumps({"status": "passed", "files": applied_relatives}, indent=2))
    return 0


def _manual_structure_findings(manual: Path, expected_witnesses: list[str]) -> list[dict[str, Any]]:
    if not manual.is_file():
        return [{"kind": "missing-manual", "path": str(manual)}]
    text = manual.read_text(encoding="utf-8")
    findings: list[dict[str, Any]] = incomplete_proof_markers(text)
    command_witnesses = [
        str(command["name"])
        for command in top_level_commands(text)
        if str(command["kind"]) in PROOF_DECLARATION_KINDS
    ]
    if command_witnesses != expected_witnesses:
        findings.append(
            {
                "kind": "top-level-witness-list-mismatch",
                "expected": expected_witnesses,
                "actual": command_witnesses,
            }
        )
    for declaration in unsafe_typing_commands(text) + rollback_control_commands(text) + unsafe_assumption_declarations(text) + forbidden_top_level_declarations(
        text,
        {"Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Notation"},
    ):
        kind = str(declaration["kind"])
        findings.append(
            {
                "kind": (
                    "unsafe-typing-control"
                    if declaration.get("unsafe_typing_control") or declaration.get("bypass_checks")
                    else "rollback-control"
                    if kind in {"Fail", "Succeed"}
                    else "assumption-declaration"
                    if kind in ASSUMPTION_DECLARATION_KINDS
                    else "forbidden-top-level"
                ),
                "declaration": kind,
                "line": declaration["line"],
            }
        )
    try:
        _prelude, lemmas = parse_manual_file(text)
        names = [str(lemma["name"]) for lemma in lemmas]
        if names != expected_witnesses:
            findings.append(
                {
                    "kind": "witness-list-mismatch",
                    "expected": expected_witnesses,
                    "actual": names,
                }
            )
        for lemma in lemmas:
            name = str(lemma["name"])
            commands = top_level_commands(str(lemma["block"]))
            if len(commands) != 1 or commands[0].get("name") != name:
                findings.append({"kind": "extra-top-level-command", "witness": name})
    except ValueError as exc:
        findings.append({"kind": "manual-parse-error", "message": str(exc)})
    return findings


def _formal_case_lib_findings(path: Path, active_theory: str) -> list[dict[str, Any]]:
    if not path.is_file():
        return [{"kind": "missing-formal-case-lib", "path": str(path)}]
    text = path.read_text(encoding="utf-8")
    uncommented = strip_coq_comments(text)
    findings: list[dict[str, Any]] = incomplete_proof_markers(text)
    for command in unsafe_typing_commands(text):
        findings.append(
            {
                "kind": "unsafe-typing-control",
                "declaration": command["kind"],
                "control": command.get("unsafe_typing_control"),
                "bypass_checks": command.get("bypass_checks", []),
                "line": command["line"],
            }
        )
    for command in rollback_control_commands(text):
        findings.append(
            {
                "kind": "rollback-control",
                "declaration": command["kind"],
                "line": command["line"],
            }
        )
    for declaration in unsafe_assumption_declarations(text):
        findings.append(
            {
                "kind": "assumption-declaration",
                "declaration": declaration["kind"],
                "line": declaration["line"],
            }
        )
    if re.search(r"(?:From|Require\s+Import).*SimpleC\.EE\.", uncommented):
        findings.append({"kind": "generated-artifact-import", "active_theory": active_theory})
    return findings


def _forbidden_findings(paths: list[Path]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for lemma in FORBIDDEN_LEMMAS:
                if re.search(rf"(?<![A-Za-z0-9_']){re.escape(lemma)}(?![A-Za-z0-9_'])", line):
                    findings.append({"path": str(path), "line": line_number, "lemma": lemma})
    return findings


def _accepted_annotation_source_findings(state: dict[str, Any]) -> list[dict[str, Any]]:
    target_c = str(state["target_files"]["c_file"])
    source = state.get("source_version") if isinstance(state.get("source_version"), dict) else {}
    expected = next(
        (
            item
            for item in source.get("files", [])
            if isinstance(item, dict) and item.get("relative_path") == target_c
        ),
        None,
    )
    current = Path(str(state["main_root"])) / target_c
    findings: list[dict[str, Any]] = []
    if not isinstance(expected, dict) or expected.get("state") != "present" or not expected.get("sha256"):
        findings.append({"kind": "missing-accepted-target-c-digest", "relative_path": target_c})
    elif not current.is_file() or _file_digest(current) != expected.get("sha256"):
        findings.append({"kind": "target-c-changed-after-annotation", "relative_path": target_c})
    accepted = state.get("accepted_rounds", {}).get("annotation", {})
    if accepted.get("source_version") != source.get("digest"):
        findings.append({"kind": "accepted-annotation-source-version-mismatch"})
    return findings


def _freshness_evidence(state: dict[str, Any]) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    refresh = Path(str(state["report_root"])) / "final-check" / "symexec-refresh"
    if refresh.exists():
        shutil.rmtree(refresh)
    refresh.mkdir(parents=True)
    symexec = run_symexec(
        main_root=main_root,
        target_c_file=Path(str(state["target_files"]["c_file"])),
        output_root=refresh,
    )
    symexec["controller_entrypoint"] = "final-check"
    mismatches: list[dict[str, Any]] = []
    if symexec.get("status") == "passed":
        for key in ("goal_file", "proof_auto_file", "goal_check_file"):
            relative = str(state["target_files"][key])
            current = main_root / relative
            generated = refresh / relative
            if not current.is_file() or not generated.is_file():
                mismatches.append({"kind": key, "relative_path": relative})
                continue
            current_text = _normalize_generated_freshness_text(current.read_text(encoding="utf-8"), main_root)
            generated_text = _normalize_generated_freshness_text(generated.read_text(encoding="utf-8"), refresh)
            if current_text != generated_text:
                mismatches.append({"kind": key, "relative_path": relative})
        current_manual = main_root / str(state["target_files"]["proof_manual_file"])
        fresh_manual = refresh / str(state["target_files"]["proof_manual_file"])
        if current_manual.is_file() and fresh_manual.is_file():
            try:
                # Canonical symbolic execution emits diagnostic split-goal blocks in
                # the raw manual.  Annotation acceptance cleans those blocks before
                # deriving source_goal_version, so freshness must compare against the
                # equivalently cleaned refresh manual rather than reject diagnostics
                # that are expected in raw symexec output.
                write_split_manual_artifacts(
                    fresh_manual,
                    diagnostics_path=refresh / str(state["target_files"]["proof_diagnostics_file"]),
                    snapshot_path=refresh / str(state["target_files"]["diagnostics_snapshot"]),
                )
                _p1, current_lemmas = parse_manual_file(current_manual.read_text(encoding="utf-8"))
                _p2, fresh_lemmas = parse_manual_file(fresh_manual.read_text(encoding="utf-8"))
                fresh_auto_lemmas = _proof_statement_hashes(refresh / str(state["target_files"]["proof_auto_file"]))
            except ValueError as exc:
                mismatches.append({"kind": "manual-parse-error", "message": str(exc)})
            else:
                current_statements = {str(item["name"]): lemma_statement_hash(item) for item in current_lemmas}
                fresh_statements = {str(item["name"]): lemma_statement_hash(item) for item in fresh_lemmas}
                if not _manual_statements_match_freshness(current_statements, fresh_statements, fresh_auto_lemmas):
                    mismatches.append({"kind": "manual-witness-statements"})
        else:
            mismatches.append({"kind": "proof_manual_file"})
    return {
        "status": "passed" if symexec.get("status") == "passed" and not mismatches else "failed",
        "symexec": {
            key: symexec.get(key)
            for key in ("status", "returncode", "first_diagnostic")
            if symexec.get(key) is not None
        },
        "mismatches": mismatches,
        "refresh_root": str(refresh),
    }


def _normalize_generated_freshness_text(text: str, root: Path) -> str:
    root = root.expanduser().resolve()
    variants = {
        str(root),
        str(root).replace("\\", "/"),
        str(root).replace("/", "\\"),
    }
    normalized = text
    for item in sorted(variants, key=len, reverse=True):
        normalized = normalized.replace(item, "$QCP_OUTPUT_ROOT")
    return normalized


def _proof_statement_hashes(path: Path) -> dict[str, str]:
    if not path.is_file():
        return {}
    try:
        _prelude, lemmas = parse_manual_file(path.read_text(encoding="utf-8"))
    except ValueError:
        return {}
    return {str(item["name"]): lemma_statement_hash(item) for item in lemmas}


def _manual_statements_match_freshness(
    current: dict[str, str],
    fresh: dict[str, str],
    fresh_auto: dict[str, str],
) -> bool:
    common = set(current) & set(fresh)
    if any(current[name] != fresh[name] for name in common):
        return False
    if set(fresh) - set(current):
        return False
    extra_current = set(current) - set(fresh)
    return all(fresh_auto.get(name) == current[name] for name in extra_current)


def _coq_side_products(main_root: Path, run_root: Path, target_files: dict[str, Any]) -> list[Path]:
    suffixes = {".vo", ".vos", ".vok", ".glob", ".aux"}
    findings: set[Path] = set()
    for key in ("formal_case_lib", "goal_file", "proof_auto_file", "proof_manual_file", "goal_check_file"):
        source = main_root / str(target_files[key])
        for suffix in (".vo", ".vos", ".vok", ".glob", ".aux"):
            candidate = source.with_suffix(suffix)
            if candidate.is_file():
                findings.add(candidate)
        hidden_aux = source.parent / f".{source.stem}.aux"
        if hidden_aux.is_file():
            findings.add(hidden_aux)
    for path in run_root.rglob("*"):
        if path.is_file() and path.suffix in suffixes and not _is_relative_to(path, run_root / "_coq_builds"):
            findings.add(path)
    return sorted(findings)


def _path_label(path: Path, main_root: Path) -> str:
    try:
        return path.relative_to(main_root).as_posix()
    except ValueError:
        return str(path)


def _remove_old_coq_side_products(
    main_root: Path,
    run_root: Path,
    target_files: dict[str, Any],
) -> dict[str, Any]:
    removed_count = 0
    error_count = 0
    first_error: str | None = None
    for path in _coq_side_products(main_root, run_root, target_files):
        try:
            path.unlink()
            removed_count += 1
        except OSError as exc:
            error_count += 1
            if first_error is None:
                first_error = f"{_path_label(path, main_root)}: {exc}"
    return {
        "removed_count": removed_count,
        "error_count": error_count,
        **({"first_error": first_error} if first_error is not None else {}),
    }


def _finish_cleanup_evidence(
    main_root: Path,
    run_root: Path,
    target_files: dict[str, Any],
    cleanup: dict[str, Any],
) -> dict[str, Any]:
    remaining = _coq_side_products(main_root, run_root, target_files)
    evidence = {
        **cleanup,
        "remaining_count": len(remaining),
        **({"first_remaining": _path_label(remaining[0], main_root)} if remaining else {}),
    }
    evidence["status"] = (
        "passed"
        if int(evidence.get("error_count", 0)) == 0 and int(evidence["remaining_count"]) == 0
        else "failed"
    )
    return evidence


def final_check(args: argparse.Namespace) -> int:
    main_root = Path(args.main_root).expanduser().resolve() if args.main_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    if state.get("final_apply", {}).get("status") != "passed":
        raise SystemExit("final-check requires a passed final-apply")
    target = state["target_files"]
    manual = main_root / target["proof_manual_file"]
    formal_case_lib = main_root / target["formal_case_lib"]
    expected = [str(item) for item in state["source_goal_version"]["target_witnesses"]]
    cleanup = _remove_old_coq_side_products(main_root, run_root, target)
    freshness = _freshness_evidence(state)
    coq = run_coqc_check(
        workspace_root=main_root,
        build_workspace=run_builds_root(run_root) / "final-check" / "src",
        target_file=Path(target["goal_check_file"]),
        target_kind="check",
        source_goal_version=str(state["source_goal_version"]["digest"]),
    )
    coq["controller_entrypoint"] = "final-check"
    manual_findings = _manual_structure_findings(manual, expected)
    lib_findings = _formal_case_lib_findings(formal_case_lib, str(target["active_case_theory"]))
    forbidden = _forbidden_findings([manual, formal_case_lib])
    accepted_source = _accepted_annotation_source_findings(state)
    cleanup = _finish_cleanup_evidence(main_root, run_root, target, cleanup)
    candidate = state["final_candidate"]
    applied_manual_matches = (
        manual.is_file()
        and bool(candidate.get("proof_manual_sha256"))
        and _file_digest(manual) == candidate.get("proof_manual_sha256")
    )
    applied_lib_matches = (
        formal_case_lib.is_file()
        and bool(candidate.get("proving_merged_lib_sha256"))
        and _file_digest(formal_case_lib) == candidate.get("proving_merged_lib_sha256")
    )
    blockers: list[dict[str, Any]] = []
    if freshness["status"] != "passed":
        blockers.append({"failure_class": "symbolic-execution-freshness", "mismatches": freshness["mismatches"]})
    if coq.get("status") != "passed":
        blockers.append({"failure_class": "fixed-coqc-check", "diagnostic": coq.get("first_diagnostic")})
    if manual_findings or not applied_manual_matches:
        blockers.append(
            {
                "failure_class": "manual-structure",
                "findings": manual_findings,
                "matches_proving_merged_manual": applied_manual_matches,
            }
        )
    if lib_findings or not applied_lib_matches:
        blockers.append(
            {
                "failure_class": "formal-case-lib-contract",
                "findings": lib_findings,
                "matches_proving_merged_lib": applied_lib_matches,
            }
        )
    if forbidden:
        blockers.append({"failure_class": "forbidden-lemma", "findings": forbidden})
    if accepted_source:
        blockers.append({"failure_class": "accepted-annotation-source", "findings": accepted_source})
    if cleanup["status"] != "passed":
        blockers.append(
            {
                "failure_class": "cleanup",
                **{
                    key: cleanup[key]
                    for key in ("error_count", "first_error", "remaining_count", "first_remaining")
                    if cleanup.get(key)
                },
            }
        )
    status = "passed" if not blockers else "failed"
    evidence = {
        "symexec_freshness": freshness,
        "coqc_check": {
            key: coq.get(key)
            for key in ("status", "returncode", "target_kind", "source_goal_version", "first_diagnostic")
            if coq.get(key) is not None
        },
        "manual_structure": {
            "status": "passed" if not manual_findings and applied_manual_matches else "failed",
            "findings": manual_findings,
            "matches_proving_merged_manual": applied_manual_matches,
        },
        "formal_case_lib_contract": {
            "status": "passed" if not lib_findings and applied_lib_matches else "failed",
            "findings": lib_findings,
            "matches_proving_merged_lib": applied_lib_matches,
        },
        "forbidden_lemmas": {
            "status": "passed" if not forbidden else "failed",
            "findings": forbidden,
        },
        "accepted_annotation_source": {
            "status": "passed" if not accepted_source else "failed",
            "findings": accepted_source,
        },
        "cleanup": cleanup,
    }
    if status == "failed":
        rollback = _rollback(state["final_apply"]["backup"])
        state["final_apply"]["rollback"] = rollback
        state["final_apply"]["status"] = "rolled-back" if rollback["status"] == "passed" else "rollback-failed"
        if rollback["status"] == "passed":
            # A retry must re-apply the pinned accepted candidate before the
            # next final check.  Returning to this phase lets `step` expose the
            # only legal recovery action instead of queuing an impossible
            # final-check against rolled-back root files.
            state["phase"] = "final-candidate-apply"
        else:
            blockers.append({"failure_class": "final-apply-rollback", "evidence": rollback})
    else:
        state["phase"] = "done"
    state["final_check"] = {
        "status": status,
        "evidence": evidence,
        "blockers": blockers,
    }
    state["current_blockers"] = blockers
    state["next_actions"] = []
    _append_event(
        run_root,
        state,
        f"final-check-{status}",
        failure_classes=[str(item.get("failure_class")) for item in blockers],
    )
    _save_state(run_root, state)
    if status == "passed":
        print(json.dumps({"status": "passed", "phase": "done"}, indent=2))
    else:
        print(json.dumps(state["final_check"], indent=2))
    return 0 if status == "passed" else 1
