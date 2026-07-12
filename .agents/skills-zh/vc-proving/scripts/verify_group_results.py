#!/usr/bin/env python3
"""Parent verify for vc-proving group worktrees."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from coq_tooling import fixed_flags_hash, make_coqc_argv, run_coqc_check, target_file_for_kind
from prepare_group_worktrees import load_group_workers_manifest
from proof_manual_utils import (
    block_has_admitted,
    case_lib_contract_errors,
    ensure_unique_lemma_names,
    helper_namespace_for_group_id,
    lemma_by_name,
    lemma_statement_hash,
    merge_case_lib,
    normalize_coq_text,
    parse_manual_file,
)
from worktree_utils import ensure_run_root, run_builds_root, slug, write_json


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.expanduser().resolve().relative_to(root.expanduser().resolve())
        return True
    except ValueError:
        return False


def _same_resolved_path(left: object, right: object) -> bool:
    return Path(str(left)).expanduser().resolve() == Path(str(right)).expanduser().resolve()


def _verification_result_dict(value: Any) -> dict[str, Any]:
    if isinstance(value, dict):
        return value
    if isinstance(value, list):
        result: dict[str, Any] = {}
        for item in value:
            if isinstance(item, dict) and item.get("kind") in {"coqc_check", "coqc"}:
                result.setdefault("coqc_check", item)
            if isinstance(item, dict) and item.get("kind") in {"coqtop_debug", "coqtop"}:
                result.setdefault("coqtop_debug", item)
        return result
    return {}


def _group_payload(group_manifest: dict[str, Any]) -> tuple[dict[str, Any], list[str]]:
    errors: list[str] = []
    handoff_files = group_manifest.get("handoff_files") if isinstance(group_manifest.get("handoff_files"), dict) else {}
    report_value = handoff_files.get("report")
    if not report_value:
        return {}, [f"{group_manifest.get('group_id', '<unknown>')}: handoff_files.report is required"]
    report_path = Path(str(report_value)).expanduser().resolve()
    if not report_path.is_file():
        return {}, [f"group_worker_report.json missing at {report_path}"]
    try:
        report = _load_json(report_path)
    except json.JSONDecodeError as exc:
        return {}, [f"group_worker_report.json is not valid JSON: {exc}"]
    if report.get("schema_version") != "qcp-group-worker-report/v1":
        errors.append("group_worker_report.json schema_version must be qcp-group-worker-report/v1")
    agent_result = report.get("agent_result") if isinstance(report.get("agent_result"), dict) else {}
    vc = agent_result.get("vc_proving") if isinstance(agent_result.get("vc_proving"), dict) else {}
    group = vc.get("group") if isinstance(vc.get("group"), dict) else {}
    if not isinstance(group, dict):
        errors.append("group_worker_report.json missing agent_result.vc_proving.group object")
        return {}, errors
    return group, errors


def _group_handoff_errors(
    *,
    manifest: dict[str, Any],
    group_manifest: dict[str, Any],
    group_worktree: Path,
    group_id: str,
) -> list[str]:
    errors: list[str] = []
    run_root_value = manifest.get("run_root")
    if run_root_value and not _is_relative_to(group_worktree, Path(str(run_root_value))):
        errors.append(f"{group_id}: group worktree is not under run root {run_root_value}")
    tooling = group_manifest.get("tooling") if isinstance(group_manifest.get("tooling"), dict) else {}
    if tooling.get("coq_tooling_only") != "yes":
        errors.append(f"{group_id}: tooling.coq_tooling_only must be yes")
    coq_workspace_root = tooling.get("coq_workspace_root")
    if not coq_workspace_root:
        errors.append(f"{group_id}: tooling.coq_workspace_root is required")
    elif not _same_resolved_path(coq_workspace_root, group_worktree):
        errors.append(f"{group_id}: tooling.coq_workspace_root does not match group worktree")
    helper = tooling.get("coq_tooling_helper")
    main_workspace_root = manifest.get("main_workspace_root")
    if main_workspace_root:
        expected_helper = Path(str(main_workspace_root)).resolve() / ".agents" / "skills" / "vc-proving" / "scripts" / "coq_tooling.py"
        if not helper:
            errors.append(f"{group_id}: tooling.coq_tooling_helper is required")
        elif not _same_resolved_path(helper, expected_helper):
            errors.append(f"{group_id}: Coq helper must come from main worktree: {expected_helper}")
    builds_root = manifest.get("coq_builds_root")
    build_workspace = tooling.get("coq_build_workspace")
    if not build_workspace:
        errors.append(f"{group_id}: tooling.coq_build_workspace is required")
    elif builds_root and not _is_relative_to(Path(str(build_workspace)), Path(str(builds_root))):
        errors.append(f"{group_id}: Coq build workspace is not under run _coq_builds root")
    if tooling.get("source_goal_version_required") != "yes":
        errors.append(f"{group_id}: tooling.source_goal_version_required must be yes")
    if tooling.get("fixed_flags_hash") != fixed_flags_hash():
        errors.append(f"{group_id}: tooling.fixed_flags_hash does not match current fixed flags")
    manual_rel = Path(str(manifest["proof_manual_file"]))
    if tooling.get("target_kind") == "group-check":
        target_value = tooling.get("coqc_check_target_file")
        if not target_value or not str(target_value).startswith(".coq_group_checks/"):
            errors.append(f"{group_id}: group-check target must be build-workspace-only .coq_group_checks file")
            expected_check = Path(".coq_group_checks/missing_group_check.v")
        else:
            expected_check = Path(str(target_value))
    else:
        expected_check = target_file_for_kind(manual_rel, "check")
        if tooling.get("coqc_check_target_file") != expected_check.as_posix():
            errors.append(f"{group_id}: tooling.coqc_check_target_file must be {expected_check.as_posix()}")
    if tooling.get("coqc_check_argv") != make_coqc_argv(expected_check):
        errors.append(f"{group_id}: tooling.coqc_check_argv does not match fixed argv")
    return errors


def _group_coqc_evidence_errors(
    group: dict[str, Any],
    *,
    manifest: dict[str, Any],
    group_manifest: dict[str, Any],
    group_id: str,
) -> list[str]:
    errors: list[str] = []
    verification = _verification_result_dict(group.get("verification_result"))
    evidence = verification.get("coqc_check")
    if not isinstance(evidence, dict):
        errors.append(f"{group_id}: missing coqc_check evidence in group report")
        return errors
    if evidence.get("status") != "passed" or evidence.get("returncode") != 0:
        errors.append(f"{group_id}: coqc_check evidence is not passed")
    tooling = group_manifest.get("tooling") if isinstance(group_manifest.get("tooling"), dict) else {}
    if evidence.get("argv") != tooling.get("coqc_check_argv"):
        errors.append(f"{group_id}: coqc_check argv does not exactly match handoff argv")
    expected_cwd = tooling.get("coq_build_workspace")
    if expected_cwd and not evidence.get("cwd"):
        errors.append(f"{group_id}: coqc_check cwd is required")
    elif expected_cwd and not _same_resolved_path(evidence.get("cwd"), expected_cwd):
        errors.append(f"{group_id}: coqc_check cwd {evidence.get('cwd')} does not match build workspace {expected_cwd}")
    expected_source_goal = manifest.get("source_goal_version")
    if expected_source_goal is not None and evidence.get("source_goal_version") != expected_source_goal:
        errors.append(
            f"{group_id}: coqc_check source_goal_version mismatch: expected {expected_source_goal}, got {evidence.get('source_goal_version')}"
        )
    if evidence.get("fixed_flags_hash") != fixed_flags_hash():
        errors.append(f"{group_id}: coqc_check fixed_flags_hash does not match current fixed flags")
    if evidence.get("target_file") != tooling.get("coqc_check_target_file"):
        errors.append(f"{group_id}: coqc_check target_file does not match handoff")
    if evidence.get("target_kind") != tooling.get("target_kind", "check"):
        errors.append(f"{group_id}: coqc_check target_kind does not match handoff")
    return errors


def _replace_blocks(seed_text: str, replacements: dict[str, str]) -> str:
    prelude, lemmas = parse_manual_file(seed_text)
    parts = [prelude]
    for lemma in lemmas:
        name = str(lemma["name"])
        block = replacements.get(name, str(lemma["block"]))
        parts.append(block if block.endswith("\n") else block + "\n")
    return "".join(parts)


def _formal_file_candidates(manual_rel: Path) -> list[Path]:
    candidates = [manual_rel]
    if manual_rel.name.endswith("_proof_manual.v"):
        base = manual_rel.name[: -len("_proof_manual.v")]
        candidates.extend(
            manual_rel.with_name(base + suffix)
            for suffix in ["_goal.v", "_proof_auto.v", "_goal_check.v", "_proof_diagnostics.v"]
        )
        candidates.append(manual_rel.with_name("diagnostics_snapshot.json"))
    return candidates


def _apply_candidate_to_round(
    *,
    workspace_root: Path,
    build_workspace: Path,
    seed_manual_path: Path,
    seed_case_lib_path: Path,
    candidate_manual: Path,
    candidate_case_lib: Path,
    source_goal_version: str | None,
    coq_timeout_seconds: int | None,
) -> tuple[bool, dict[str, Any]]:
    original_manual_text = seed_manual_path.read_text(encoding="utf-8")
    original_case_lib_text = seed_case_lib_path.read_text(encoding="utf-8")
    seed_manual_path.write_text(candidate_manual.read_text(encoding="utf-8"), encoding="utf-8")
    seed_case_lib_path.write_text(candidate_case_lib.read_text(encoding="utf-8"), encoding="utf-8")
    manual_rel = seed_manual_path.relative_to(workspace_root)
    coq_evidence = run_coqc_check(
        workspace_root=workspace_root,
        build_workspace=build_workspace,
        target_file=target_file_for_kind(manual_rel, "check"),
        target_kind="check",
        source_goal_version=source_goal_version,
        timeout_seconds=coq_timeout_seconds,
    )
    final_ok = coq_evidence.get("status") == "passed"
    if not final_ok:
        seed_manual_path.write_text(original_manual_text, encoding="utf-8")
        seed_case_lib_path.write_text(original_case_lib_text, encoding="utf-8")
    return final_ok, coq_evidence


def verify_and_merge(
    manifest_path: Path,
    *,
    main_workspace_root: Path | None = None,
    round_check_file: str | None = None,
    coq_timeout_seconds: int | None = None,
) -> dict[str, Any]:
    manifest = _load_json(manifest_path)
    round_worktree = Path(str(manifest["round_worktree"])).resolve()
    if main_workspace_root is None:
        if not manifest.get("main_workspace_root"):
            raise SystemExit("manifest.main_workspace_root is required so parent Coq verification can locate helper contracts")
        main_workspace_root = Path(str(manifest["main_workspace_root"])).resolve()
    else:
        manifest["main_workspace_root"] = str(main_workspace_root.resolve())
    work_dir = Path(str(manifest["work_dir"])).resolve()
    manual_rel = Path(str(manifest["proof_manual_file"]))
    case_lib_rel = Path(str(manifest["case_lib"]))
    seed_manual_path = round_worktree / manual_rel
    seed_case_lib_path = round_worktree / case_lib_rel
    seed_manual_text = seed_manual_path.read_text(encoding="utf-8")
    seed_case_lib_text = seed_case_lib_path.read_text(encoding="utf-8")
    _prelude, seed_lemmas = parse_manual_file(seed_manual_text)
    ensure_unique_lemma_names(seed_lemmas)
    seed_map = lemma_by_name(seed_lemmas)
    seed_names = set(seed_map)
    target_witnesses = [str(item) for item in manifest.get("target_witnesses", [])]
    groups = load_group_workers_manifest(manifest_path)
    run_root = (
        Path(str(manifest["run_root"])).resolve()
        if manifest.get("run_root")
        else ensure_run_root(main_workspace_root, str(manifest.get("case_name") or manual_rel.parent.name), path_hint=round_worktree)
    )
    coq_builds_root = Path(str(manifest.get("coq_builds_root") or run_builds_root(run_root))).resolve()
    manifest["coq_builds_root"] = str(coq_builds_root)
    parent_build_workspace = coq_builds_root / slug(round_worktree.name) / "parent" / "src"
    if round_check_file is not None:
        expected_round_check_file = Path(round_check_file)
    else:
        expected_round_check_file = Path(str(manifest.get("round_check_file") or target_file_for_kind(manual_rel, "check")))
    if expected_round_check_file != target_file_for_kind(manual_rel, "check"):
        raise SystemExit(f"round check file must match current proof manual: {target_file_for_kind(manual_rel, 'check')}")

    replacements: dict[str, str] = {}
    solved: list[str] = []
    unsolved: list[str] = []
    blockers: list[dict[str, Any]] = []
    errors: list[str] = []
    group_lib_texts: list[tuple[str, str, dict[str, Any]]] = []
    worker_groups: list[dict[str, Any]] = []

    for group_manifest in groups:
        group_id = str(group_manifest["group_id"])
        try:
            expected_helper_namespace = helper_namespace_for_group_id(group_id)
        except ValueError as exc:
            errors.append(str(exc))
            expected_helper_namespace = {}
        group_worktree = Path(str(group_manifest["worktree_path"]))
        assigned = [str(item) for item in group_manifest.get("witness_names", [])]
        assigned_set = set(assigned)
        helper_namespace = (
            group_manifest.get("helper_namespace")
            if isinstance(group_manifest.get("helper_namespace"), dict)
            else {}
        )
        group_report, report_errors = _group_payload(group_manifest)
        report_helper_namespace = (
            group_report.get("helper_namespace")
            if isinstance(group_report.get("helper_namespace"), dict)
            else {}
        )
        reported_assigned = (
            {str(item) for item in group_report.get("assigned_witnesses", [])}
            if isinstance(group_report.get("assigned_witnesses"), list)
            else set()
        )
        reported_solved = (
            {str(item) for item in group_report.get("solved_witnesses", [])}
            if isinstance(group_report.get("solved_witnesses"), list)
            else set()
        )
        reported_unsolved = (
            {str(item) for item in group_report.get("unsolved_witnesses", [])}
            if isinstance(group_report.get("unsolved_witnesses"), list)
            else set()
        )
        group_blockers = group_report.get("blockers") if isinstance(group_report.get("blockers"), list) else []
        group_errors = group_report.get("errors") if isinstance(group_report.get("errors"), list) else []
        worker_groups.append(
            {
                "group_id": group_id,
                "assigned_witnesses": assigned,
                "reported_solved_witnesses": sorted(reported_solved),
                "blockers": group_blockers,
                "errors": group_errors,
                "worktree_path": str(group_worktree),
                "helper_namespace": helper_namespace,
            }
        )
        handoff_errors = _group_handoff_errors(
            manifest=manifest,
            group_manifest=group_manifest,
            group_worktree=group_worktree,
            group_id=group_id,
        )
        report_contract_errors = list(report_errors)
        if group_report.get("status") != "completed":
            report_contract_errors.append(f"{group_id}: group report status must be completed")
        if helper_namespace != expected_helper_namespace:
            report_contract_errors.append(f"{group_id}: group manifest helper_namespace does not match group_id suffix policy")
        if report_helper_namespace != helper_namespace:
            report_contract_errors.append(f"{group_id}: group report helper_namespace does not match group handoff")
        if not isinstance(group_report.get("case_lib_added_declarations"), list):
            report_contract_errors.append(f"{group_id}: group report case_lib_added_declarations must be a list")
        if reported_assigned != assigned_set:
            report_contract_errors.append(f"{group_id}: group report assigned_witnesses do not match group handoff")
        if not reported_solved <= assigned_set:
            report_contract_errors.append(f"{group_id}: solved_witnesses contains unassigned witnesses")
        if not reported_unsolved <= assigned_set:
            report_contract_errors.append(f"{group_id}: unsolved_witnesses contains unassigned witnesses")
        if reported_solved & reported_unsolved:
            report_contract_errors.append(f"{group_id}: solved_witnesses and unsolved_witnesses overlap")
        candidate = group_report.get("candidate") if isinstance(group_report.get("candidate"), dict) else {}
        for key, value in candidate.items():
            if not value:
                continue
            candidate_path = Path(str(value))
            if candidate_path.is_absolute() and not _is_relative_to(candidate_path, group_worktree):
                report_contract_errors.append(f"{group_id}: candidate.{key} is outside group worktree")
        expected_source_goal = manifest.get("source_goal_version")
        if expected_source_goal is not None and group_report.get("source_goal_version") != expected_source_goal:
            report_contract_errors.append(
                f"{group_id}: group report source_goal_version mismatch: expected {expected_source_goal}, got {group_report.get('source_goal_version')}"
            )
        if handoff_errors or report_contract_errors:
            errors.extend(handoff_errors)
            errors.extend(report_contract_errors)
            unsolved.extend(name for name in assigned if name not in unsolved)
            continue
        if group_errors or group_blockers:
            blockers.extend({**item, "group_id": group_id} for item in group_blockers if isinstance(item, dict))
            for name in assigned:
                if name not in unsolved:
                    unsolved.append(name)
            continue
        coq_evidence_errors = _group_coqc_evidence_errors(
            group_report,
            manifest=manifest,
            group_manifest=group_manifest,
            group_id=group_id,
        )
        if coq_evidence_errors:
            errors.extend(coq_evidence_errors)
            unsolved.extend(name for name in assigned if name not in unsolved)
            continue

        group_manual_path = group_worktree / manual_rel
        group_case_lib_path = group_worktree / case_lib_rel
        if not group_manual_path.is_file():
            errors.append(f"{group_id}: proof manual missing in group worktree")
            unsolved.extend(name for name in assigned if name not in unsolved)
            continue
        if not group_case_lib_path.is_file():
            errors.append(f"{group_id}: case_lib missing in group worktree")
            unsolved.extend(name for name in assigned if name not in unsolved)
            continue
        generated_file_errors: list[str] = []
        for rel in _formal_file_candidates(manual_rel):
            if rel == manual_rel:
                continue
            round_file = round_worktree / rel
            group_file = group_worktree / rel
            if round_file.is_file() and not group_file.is_file():
                generated_file_errors.append(f"{group_id}: generated file missing in group worktree: {rel}")
            elif round_file.is_file() and group_file.read_text(encoding="utf-8") != round_file.read_text(encoding="utf-8"):
                generated_file_errors.append(f"{group_id}: generated file modified in group worktree: {rel}")
            elif not round_file.exists() and group_file.exists():
                generated_file_errors.append(f"{group_id}: group worktree added generated file: {rel}")
        if generated_file_errors:
            errors.extend(generated_file_errors)
            unsolved.extend(name for name in assigned if name not in unsolved)
            continue

        group_manual_text = group_manual_path.read_text(encoding="utf-8")
        _group_prelude, group_lemmas = parse_manual_file(group_manual_text)
        ensure_unique_lemma_names(group_lemmas)
        group_map = lemma_by_name(group_lemmas)
        extra_manual = set(group_map) - seed_names
        if extra_manual:
            errors.append(f"{group_id}: proof manual added helper/top-level lemmas: {', '.join(sorted(extra_manual))}")
            unsolved.extend(name for name in assigned if name not in unsolved)
            continue
        unassigned_errors: list[str] = []
        for name, seed in seed_map.items():
            if name in assigned_set:
                continue
            group_lemma = group_map.get(name)
            if group_lemma is None:
                unassigned_errors.append(f"{group_id}: unassigned witness block `{name}` missing")
            elif normalize_coq_text(str(seed["block"])) != normalize_coq_text(str(group_lemma["block"])):
                unassigned_errors.append(f"{group_id}: unassigned witness block `{name}` changed")
        if unassigned_errors:
            errors.extend(unassigned_errors)
            unsolved.extend(name for name in assigned if name not in unsolved)
            continue

        for name in assigned:
            seed = seed_map.get(name)
            group_lemma = group_map.get(name)
            if seed is None or group_lemma is None:
                errors.append(f"{group_id}: assigned witness `{name}` missing")
                unsolved.append(name)
                continue
            if name not in reported_solved:
                unsolved.append(name)
                continue
            if lemma_statement_hash(seed) != lemma_statement_hash(group_lemma):
                errors.append(f"{group_id}: witness statement changed for `{name}`")
                unsolved.append(name)
                continue
            block = str(group_lemma["block"])
            if block_has_admitted(block):
                errors.append(f"{group_id}: solved witness `{name}` still contains Admitted.")
                unsolved.append(name)
                continue
            replacements[name] = block
            if name not in solved:
                solved.append(name)
        group_lib_texts.append((group_id, group_case_lib_path.read_text(encoding="utf-8"), helper_namespace))

    auto_manual_text = _replace_blocks(seed_manual_text, replacements)
    merged_case_lib, added_decls, lib_errors = merge_case_lib(seed_case_lib_text, group_lib_texts)
    for name in target_witnesses:
        if name not in solved and name not in unsolved:
            unsolved.append(name)

    candidate_manual_text = auto_manual_text
    candidate_case_lib_text = merged_case_lib
    errors.extend(f"case-lib-merge-validation: {error}" for error in lib_errors)
    case_lib_merge = {
        "policy": "deterministic-group-id-suffixed",
        "helper_namespace_required": "yes",
        "added_declarations": added_decls,
        "errors": lib_errors,
    }

    merge_ready = not errors and not blockers and set(solved) == set(target_witnesses)
    candidate_dir = work_dir / "candidate"
    candidate_manual = candidate_dir / manual_rel
    candidate_case_lib = candidate_dir / case_lib_rel
    candidate_manual.parent.mkdir(parents=True, exist_ok=True)
    candidate_case_lib.parent.mkdir(parents=True, exist_ok=True)
    candidate_manual.write_text(candidate_manual_text, encoding="utf-8")
    candidate_case_lib.write_text(candidate_case_lib_text, encoding="utf-8")

    parent_coq_evidence: dict[str, Any] | None = None
    if merge_ready:
        final_ok, parent_coq_evidence = _apply_candidate_to_round(
            workspace_root=round_worktree,
            build_workspace=parent_build_workspace,
            seed_manual_path=seed_manual_path,
            seed_case_lib_path=seed_case_lib_path,
            candidate_manual=candidate_manual,
            candidate_case_lib=candidate_case_lib,
            source_goal_version=manifest.get("source_goal_version"),
            coq_timeout_seconds=coq_timeout_seconds,
        )
        if not final_ok:
            merge_ready = False
            errors.append("merged round candidate failed coqc_check")

    group_merged_result = {
        "schema_version": "qcp-vc-proving-group-merged-result/v1",
        "kind": "qcp-vc-proving-group-merged-result",
        "status": "completed" if merge_ready else "blocked",
        "solved_witnesses": solved,
        "unsolved_witnesses": unsolved,
        "candidate": {
            "proof_manual_file": str(candidate_manual),
            "case_lib": str(candidate_case_lib),
            "round_worktree_proof_manual_file": str(seed_manual_path),
            "round_worktree_case_lib": str(seed_case_lib_path),
        },
        "worker_groups": worker_groups,
        "case_lib_added_declarations": added_decls,
        "case_lib_merge": case_lib_merge,
        "verification_result": {
            "coqc_check": parent_coq_evidence
            if parent_coq_evidence is not None
            else {"status": "skipped", "reason": "merged candidate was not ready for parent coqc_check"}
        },
        "blockers": blockers,
        "errors": errors,
        "merge_vc_ready": "yes" if merge_ready else "no",
    }
    agent_result = {
        "schema_version": "qcp-vc-proving-agent-result/v1",
        "kind": "qcp-vc-proving",
        "status": "completed" if merge_ready else "blocked",
        "source_version": {
            "source_goal_version": manifest.get("source_goal_version"),
            "target_witnesses": target_witnesses,
        },
        "group_merged_result": group_merged_result,
        "blockers": blockers,
        "errors": errors,
        "merge_vc_ready": "yes" if merge_ready else "no",
    }
    report = {
        "schema_version": "qcp-vc-proving-parent-verify-result/v1",
        "kind": "qcp-vc-proving-parent-verify-result",
        "agent_result": {"vc_proving": agent_result},
        "group_merged_result": group_merged_result,
    }
    report_path = Path(str(manifest.get("group_merged_result_file") or (Path(str(manifest["round_report_directory"])).resolve() / "group_merged_result.json")))
    write_json(report_path, report)
    print(json.dumps(report, indent=2, ensure_ascii=True))
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify group worktrees and merge vc-proving candidates.")
    parser.add_argument("manifest", help="Path to group_workers_manifest.json")
    parser.add_argument("--main-workspace-root", default=None, help="Main worktree root for contract validation")
    parser.add_argument("--round-check-file", default=None, help="Full current-round Coq check file")
    parser.add_argument("--coq-timeout-seconds", type=int, default=None)
    args = parser.parse_args()
    report = verify_and_merge(
        Path(args.manifest).expanduser().resolve(),
        main_workspace_root=Path(args.main_workspace_root).expanduser().resolve() if args.main_workspace_root else None,
        round_check_file=args.round_check_file,
        coq_timeout_seconds=args.coq_timeout_seconds,
    )
    vc = report["agent_result"]["vc_proving"]
    return 0 if vc.get("merge_vc_ready") == "yes" else 1


if __name__ == "__main__":
    raise SystemExit(main())
