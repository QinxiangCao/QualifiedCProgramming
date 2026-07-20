#!/usr/bin/env python3
"""Verify compact group results and build a deterministic proving_merged candidate."""

# ruff: noqa: E402 -- internal sibling modules are resolved from this script directory.

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from coq_tooling import infer_case_config, run_coqc_check
from path_utils import coq_identifier_slug, run_builds_root, slug, write_json
from prepare_group_workers import load_group_workers_manifest
from proof_manual_utils import (
    block_has_admitted,
    ensure_unique_lemma_names,
    helper_namespace_for_group_id,
    forbidden_top_level_declarations,
    lemma_by_name,
    lemma_statement_hash,
    merge_group_worker_libs,
    normalize_coq_text,
    parse_manual_file,
    rollback_control_commands,
    top_level_commands,
    unsafe_assumption_declarations,
    unsafe_typing_commands,
)


FORBIDDEN_LEMMAS = (
    "logic_equiv_refl",
    "elim_wand_emp_emp",
    "logic_equiv_symm",
    "sepcon_emp_logic_equiv'",
    "logic_equiv_andp_comm",
    "logic_equiv_sepcon_comm",
    "logic_equiv_sepcon_emp",
    "logic_equiv_andp_truep",
    "logic_equiv_truep_andp",
    "truep_andp_right_equiv",
    "logic_equiv_orp_comm",
    "logic_equiv_trans",
    "logic_equiv_orp_assoc",
    "logic_equiv_sepcon_assoc",
    "logic_equiv_andp_assoc",
    "logic_equiv_sepcon_orp",
    "logic_equiv_sepcon_orp_distr",
    "logic_equiv_orp_sepcon",
    "derivable1_trans",
    "derivable1_refl",
    "derivable1_sepcon_comm",
    "coq_prop_andp_right",
    "derivable1_sepcon_mono",
)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise SystemExit(f"JSON file must contain an object: {path}")
    return payload


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.expanduser().resolve().relative_to(root.expanduser().resolve())
        return True
    except ValueError:
        return False


def _replace_blocks(seed_text: str, replacements: dict[str, str]) -> str:
    prelude, lemmas = parse_manual_file(seed_text)
    parts = [prelude]
    for lemma in lemmas:
        block = replacements.get(str(lemma["name"]), str(lemma["block"]))
        parts.append(block if block.endswith("\n") else block + "\n")
    return "".join(parts)


def _forbidden_findings(path: Path) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        for lemma in FORBIDDEN_LEMMAS:
            if re.search(rf"(?<![A-Za-z0-9_']){re.escape(lemma)}(?![A-Za-z0-9_'])", line):
                findings.append({"path": str(path), "line": line_number, "lemma": lemma})
    return findings


def _group_layout_errors(group: dict[str, Any], groups_directory: Path, report_directory: Path) -> list[str]:
    group_id = str(group.get("id") or "")
    directory = Path(str(group.get("directory", ""))).resolve()
    manual = Path(str(group.get("proof_manual", ""))).resolve()
    worker_lib = Path(str(group.get("group_worker_lib", ""))).resolve()
    errors: list[str] = []
    expected_name = f"group_{int(group.get('index', -1)):02d}__{slug(group_id)}"
    if directory.parent != groups_directory or directory.name != expected_name:
        errors.append(f"{group_id}: invalid fixed group directory")
    if manual.parent != directory or worker_lib.parent != directory:
        errors.append(f"{group_id}: copied manual and group_worker_lib must be direct children of the group directory")
    expected_files = {manual.name, worker_lib.name}
    actual_files = {path.name for path in directory.iterdir()} if directory.is_dir() else set()
    if actual_files != expected_files:
        errors.append(f"{group_id}: group directory must contain only manual and group_worker_lib")
    expected_report = report_directory / "groups" / directory.name
    if Path(str(group.get("report_directory", ""))).resolve() != expected_report:
        errors.append(f"{group_id}: invalid group report directory")
    for name in ("group_worker_input.md", "group_worker_report.json", "group_worker_output.md"):
        if not (expected_report / name).is_file():
            errors.append(f"{group_id}: missing {name}")
    return errors


def _group_check(
    *,
    main_root: Path,
    run_root: Path,
    round_id: str,
    group: dict[str, Any],
    proof_manual_rel: Path,
    formal_case_lib_rel: Path,
    source_goal_version: str,
) -> dict[str, Any]:
    directory = Path(str(group["directory"]))
    config = infer_case_config(main_root, (main_root / proof_manual_rel).parent)
    proof_manual_module = proof_manual_rel.stem
    goal_module = proof_manual_module.replace("_proof_manual", "_goal")
    proof_auto_module = proof_manual_module.replace("_proof_manual", "_proof_auto")
    target = (
        Path(".coq_group_checks")
        / f"{proof_manual_module}_{coq_identifier_slug(directory.name)}_check.v"
    )
    return run_coqc_check(
        workspace_root=main_root,
        build_workspace=run_builds_root(run_root) / round_id / directory.name / "src",
        target_file=target,
        target_kind="group-check",
        source_goal_version=source_goal_version,
        group_check={
            "case_theory": config["active_theory"],
            "require_modules": [
                goal_module,
                proof_auto_module,
                proof_manual_module,
            ],
            "assigned_witnesses": [str(name) for name in group["witnesses"]],
        },
        overlays={
            proof_manual_rel: Path(str(group["proof_manual"])),
            formal_case_lib_rel: Path(str(group["group_worker_lib"])),
        },
    )


def _compact_check(evidence: dict[str, Any]) -> dict[str, Any]:
    return {
        key: evidence.get(key)
        for key in ("status", "returncode", "target_kind", "source_goal_version", "first_diagnostic")
        if evidence.get(key) is not None
    }


def _compact_declarations(items: list[dict[str, str]]) -> list[dict[str, str]]:
    keys = ("name", "kind", "group_id", "statement_hash", "helper_namespace_suffix")
    return [{key: str(item[key]) for key in keys if key in item} for item in items]


def _manifest_context(manifest_path: Path, main_root: Path) -> dict[str, Any]:
    manifest_path = manifest_path.expanduser().resolve()
    main_root = main_root.expanduser().resolve()
    try:
        report_relative = manifest_path.relative_to(main_root / "reports")
    except ValueError as exc:
        raise SystemExit("group_workers_manifest is outside the fixed report root") from exc
    if (
        len(report_relative.parts) != 4
        or report_relative.parts[1] != "rounds"
        or report_relative.parts[3] != "group_workers_manifest.json"
    ):
        raise SystemExit("group_workers_manifest does not use the fixed report layout")
    run_id, _rounds, report_round, _name = report_relative.parts
    manifest = _load_json(manifest_path)
    if manifest.get("schema_version") != "qcp-vc-proving-group-workers-manifest/v3":
        raise SystemExit("group_workers_manifest schema_version must be qcp-vc-proving-group-workers-manifest/v3")
    if not isinstance(manifest.get("groups"), list) or not manifest["groups"] or not all(
        isinstance(item, dict) for item in manifest["groups"]
    ):
        raise SystemExit("group_workers_manifest groups must be a non-empty object list")
    round_id = str(manifest.get("round") or "")
    if not round_id or round_id != report_round:
        raise SystemExit("group_workers_manifest round does not match its fixed report directory")
    run_root = (main_root / "verification_runs" / run_id).resolve()
    if run_root.parent != main_root / "verification_runs" or not run_root.is_dir():
        raise SystemExit("group_workers_manifest run root is missing or invalid")
    vc_directory = run_root / round_id
    expected_base = (vc_directory / "base_manifest.json").resolve()
    base_path = Path(str(manifest.get("base_manifest") or "")).expanduser().resolve()
    if base_path != expected_base:
        raise SystemExit("group_workers_manifest base_manifest does not use the fixed vc-proving path")
    base = _load_json(base_path)
    if base.get("schema_version") != "qcp-vc-proving-base-manifest/v2":
        raise SystemExit("invalid base manifest schema_version")
    if base.get("round") != round_id or vc_directory.name != round_id:
        raise SystemExit("base manifest round mismatch")
    if manifest.get("source_goal_version") != base.get("source_goal_version"):
        raise SystemExit("group_workers_manifest source_goal_version is stale")
    proof_manual_rel = Path(str(base.get("proof_manual") or ""))
    formal_case_lib_rel = Path(str(base.get("formal_case_lib") or ""))
    for label, relative in (("proof_manual", proof_manual_rel), ("formal_case_lib", formal_case_lib_rel)):
        if relative.is_absolute() or ".." in relative.parts or not relative.parts or relative.parts[0] != "SeparationLogic":
            raise SystemExit(f"base manifest {label} must be a formal repository-relative path")
    return {
        "manifest": manifest,
        "base": base,
        "run_root": run_root,
        "vc_directory": vc_directory,
        "report_directory": manifest_path.parent,
        "round_id": round_id,
        "proof_manual_rel": proof_manual_rel,
        "formal_case_lib_rel": formal_case_lib_rel,
    }


def _validate_group_candidate_content(
    group: dict[str, Any],
    *,
    seed_prelude: str,
    seed_map: dict[str, dict[str, Any]],
    seed_lib_text: str,
    groups_directory: Path,
    report_directory: Path,
) -> dict[str, Any]:
    group_id = str(group.get("id") or "")
    assigned = [str(item) for item in group.get("witnesses", [])]
    errors = _group_layout_errors(group, groups_directory, report_directory)
    if not assigned or len(assigned) != len(set(assigned)):
        errors.append(f"{group_id}: assigned witnesses must be non-empty and unique")
    try:
        expected_namespace = helper_namespace_for_group_id(group_id)
    except ValueError as exc:
        errors.append(str(exc))
        expected_namespace = {}
    if group.get("helper_namespace") != expected_namespace:
        errors.append(f"{group_id}: helper namespace mismatch")
    group_manual = Path(str(group.get("proof_manual") or ""))
    group_worker_lib = Path(str(group.get("group_worker_lib") or ""))
    group_map: dict[str, dict[str, Any]] = {}
    group_worker_lib_text = ""
    try:
        group_prelude, group_lemmas = parse_manual_file(group_manual.read_text(encoding="utf-8"))
        ensure_unique_lemma_names(group_lemmas)
        group_map = lemma_by_name(group_lemmas)
        if normalize_coq_text(group_prelude) != normalize_coq_text(seed_prelude):
            errors.append(f"{group_id}: copied manual prelude changed")
    except (OSError, ValueError) as exc:
        errors.append(f"{group_id}: copied manual cannot be parsed: {exc}")
    if set(group_map) != set(seed_map):
        errors.append(f"{group_id}: copied manual declaration set changed")
    else:
        changed_unassigned = [
            name
            for name, seed_lemma in seed_map.items()
            if name not in assigned
            and normalize_coq_text(str(seed_lemma["block"])) != normalize_coq_text(str(group_map[name]["block"]))
        ]
        if changed_unassigned:
            errors.append(f"{group_id}: unassigned witnesses changed: {', '.join(changed_unassigned)}")
        for name in assigned:
            seed_lemma = seed_map.get(name)
            candidate = group_map.get(name)
            if seed_lemma is None or candidate is None:
                errors.append(f"{group_id}: assigned witness `{name}` is missing")
            elif lemma_statement_hash(seed_lemma) != lemma_statement_hash(candidate):
                errors.append(f"{group_id}: witness statement changed for `{name}`")
            elif block_has_admitted(str(candidate["block"])):
                errors.append(f"{group_id}: witness `{name}` contains Admitted/Abort")
            else:
                commands = top_level_commands(str(candidate["block"]))
                if len(commands) != 1 or commands[0].get("kind") not in {
                    "Lemma",
                    "Theorem",
                    "Proposition",
                    "Corollary",
                    "Example",
                    "Fact",
                    "Remark",
                } or commands[0].get("name") != name:
                    errors.append(f"{group_id}: witness `{name}` contains an extra top-level command")
    manual_forbidden = unsafe_typing_commands(
        group_manual.read_text(encoding="utf-8") if group_manual.is_file() else ""
    ) + rollback_control_commands(
        group_manual.read_text(encoding="utf-8") if group_manual.is_file() else ""
    ) + unsafe_assumption_declarations(
        group_manual.read_text(encoding="utf-8") if group_manual.is_file() else ""
    ) + forbidden_top_level_declarations(
        group_manual.read_text(encoding="utf-8") if group_manual.is_file() else "",
        {"Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Notation"},
    )
    if manual_forbidden:
        errors.append(f"{group_id}: copied manual contains forbidden top-level declarations")
    try:
        group_worker_lib_text = group_worker_lib.read_text(encoding="utf-8")
    except OSError as exc:
        errors.append(f"{group_id}: group_worker_lib cannot be read: {exc}")
    else:
        _merged, _added, lib_errors = merge_group_worker_libs(
            seed_lib_text,
            [(group_id, group_worker_lib_text, expected_namespace)],
        )
        errors.extend(f"{group_id}: group_worker_lib contract: {error}" for error in lib_errors)
    forbidden: list[dict[str, Any]] = []
    for path in (group_manual, group_worker_lib):
        if path.is_file():
            forbidden.extend(_forbidden_findings(path))
    if forbidden:
        errors.append(f"{group_id}: group candidate uses forbidden lemmas")
    return {
        "errors": errors,
        "group_map": group_map,
        "group_worker_lib_text": group_worker_lib_text,
        "expected_namespace": expected_namespace,
    }


def validate_group_for_acceptance(
    manifest_path: Path,
    *,
    group_id: str,
    main_root: Path,
    expected_proof_manual: str,
    expected_formal_case_lib: str,
) -> list[str]:
    """Validate one group copy before controller marks the group accepted."""

    main_root = main_root.expanduser().resolve()
    context = _manifest_context(manifest_path, main_root)
    base = context["base"]
    errors: list[str] = []
    if base.get("proof_manual") != expected_proof_manual or base.get("formal_case_lib") != expected_formal_case_lib:
        errors.append("vc-proving base manifest does not match current target formal paths")
    formal_manual = main_root / context["proof_manual_rel"]
    formal_case_lib = main_root / context["formal_case_lib_rel"]
    seed = base.get("seed_sha256") if isinstance(base.get("seed_sha256"), dict) else {}
    if not formal_manual.is_file() or seed.get("proof_manual") != _sha256(formal_manual):
        errors.append("formal proof manual changed after vc-proving preparation")
    if not formal_case_lib.is_file() or seed.get("formal_case_lib") != _sha256(formal_case_lib):
        errors.append("formal_case_lib changed after vc-proving preparation")
    if errors:
        return errors
    seed_prelude, seed_lemmas = parse_manual_file(formal_manual.read_text(encoding="utf-8"))
    ensure_unique_lemma_names(seed_lemmas)
    seed_map = lemma_by_name(seed_lemmas)
    group = next(
        (item for item in context["manifest"].get("groups", []) if str(item.get("id")) == group_id),
        None,
    )
    if not isinstance(group, dict):
        return [f"{group_id}: group missing from current manifest"]
    result = _validate_group_candidate_content(
        group,
        seed_prelude=seed_prelude,
        seed_map=seed_map,
        seed_lib_text=formal_case_lib.read_text(encoding="utf-8"),
        groups_directory=context["vc_directory"] / "groups",
        report_directory=context["report_directory"],
    )
    return [str(item) for item in result["errors"]]


def verify_and_merge(
    manifest_path: Path,
    *,
    main_root: Path | None = None,
    coq_timeout_seconds: int | None = None,
) -> dict[str, Any]:
    manifest_path = manifest_path.expanduser().resolve()
    if main_root is None:
        try:
            report_relative = manifest_path.parents[3]
        except IndexError as exc:
            raise SystemExit("cannot infer main root from group_workers_manifest") from exc
        if report_relative.name != "reports":
            raise SystemExit("--main-root is required for a manifest outside the fixed report root")
        main_root = report_relative.parent
    main_root = main_root.expanduser().resolve()
    context = _manifest_context(manifest_path, main_root)
    manifest = context["manifest"]
    base = context["base"]
    vc_directory = context["vc_directory"]
    run_root = context["run_root"]
    round_id = context["round_id"]
    report_directory = context["report_directory"]
    proof_manual_rel = context["proof_manual_rel"]
    formal_case_lib_rel = context["formal_case_lib_rel"]
    formal_manual = main_root / proof_manual_rel
    formal_case_lib = main_root / formal_case_lib_rel
    seed = base.get("seed_sha256") if isinstance(base.get("seed_sha256"), dict) else {}
    if seed.get("proof_manual") != _sha256(formal_manual) or seed.get("formal_case_lib") != _sha256(formal_case_lib):
        raise SystemExit("formal seed changed after vc-proving preparation")
    seed_manual_text = formal_manual.read_text(encoding="utf-8")
    seed_lib_text = formal_case_lib.read_text(encoding="utf-8")
    seed_prelude, seed_lemmas = parse_manual_file(seed_manual_text)
    ensure_unique_lemma_names(seed_lemmas)
    seed_map = lemma_by_name(seed_lemmas)
    target_witnesses = [str(item["name"]) for item in base.get("witnesses", [])]

    replacements: dict[str, str] = {}
    solved: list[str] = []
    errors: list[str] = []
    blockers: list[Any] = []
    group_summaries: list[dict[str, Any]] = []
    group_lib_texts: list[tuple[str, str, dict[str, Any]]] = []
    groups_directory = vc_directory / "groups"

    for group in load_group_workers_manifest(manifest_path):
        group_id = str(group["id"])
        assigned = [str(item) for item in group.get("witnesses", [])]
        content = _validate_group_candidate_content(
            group,
            seed_prelude=seed_prelude,
            seed_map=seed_map,
            seed_lib_text=seed_lib_text,
            groups_directory=groups_directory,
            report_directory=report_directory,
        )
        group_errors = [str(item) for item in content["errors"]]
        report_path = Path(str(group["report_directory"])) / "group_worker_report.json"
        try:
            report = _load_json(report_path)
        except (OSError, json.JSONDecodeError, SystemExit) as exc:
            report = {}
            group_errors.append(f"{group_id}: invalid group report: {exc}")
        if report.get("schema_version") != "qcp-group-worker-report/v2":
            group_errors.append(f"{group_id}: invalid group report schema_version")
        extra_report_fields = set(report) - {"schema_version", "status", "source_goal_version", "blockers"}
        if extra_report_fields:
            group_errors.append(f"{group_id}: unsupported group report fields: {sorted(extra_report_fields)}")
        if report.get("status") != "completed":
            group_errors.append(f"{group_id}: group report status must be completed")
        if report.get("source_goal_version") != base.get("source_goal_version"):
            group_errors.append(f"{group_id}: stale group report")
        if report.get("blockers"):
            blockers.extend(report["blockers"] if isinstance(report["blockers"], list) else [report["blockers"]])
            group_errors.append(f"{group_id}: group report contains blockers")
        check: dict[str, Any] = {"status": "skipped"}
        if not group_errors:
            check = _group_check(
                main_root=main_root,
                run_root=run_root,
                round_id=round_id,
                group=group,
                proof_manual_rel=proof_manual_rel,
                formal_case_lib_rel=formal_case_lib_rel,
                source_goal_version=str(base["source_goal_version"]),
            )
            if check.get("status") != "passed":
                group_errors.append(f"{group_id}: fixed group check failed")
        summary = {"id": group_id, "status": "passed" if not group_errors else "failed", "check": _compact_check(check)}
        group_summaries.append(summary)
        if group_errors:
            errors.extend(group_errors)
            continue

        group_map = content["group_map"]
        for name in assigned:
            replacements[name] = str(group_map[name]["block"])
            solved.append(name)
        group_lib_texts.append(
            (
                group_id,
                str(content["group_worker_lib_text"]),
                content["expected_namespace"],
            )
        )

    merged_manual_text = _replace_blocks(seed_manual_text, replacements)
    merged_lib_text, added_declarations, lib_errors = merge_group_worker_libs(seed_lib_text, group_lib_texts)
    errors.extend(f"group_worker_lib merge: {error}" for error in lib_errors)
    proving_merged_directory = vc_directory / "proving_merged"
    proving_merged_directory.mkdir(parents=True, exist_ok=True)
    merged_manual = proving_merged_directory / formal_manual.name
    proving_merged_lib = proving_merged_directory / formal_case_lib.name
    merged_manual.write_text(merged_manual_text, encoding="utf-8")
    proving_merged_lib.write_text(merged_lib_text, encoding="utf-8")
    forbidden = _forbidden_findings(merged_manual) + _forbidden_findings(proving_merged_lib)
    if forbidden:
        errors.append("proving_merged candidate uses forbidden lemmas")

    ready = not errors and not blockers and set(solved) == set(target_witnesses)
    parent_check: dict[str, Any] = {"status": "skipped"}
    if ready:
        proof_manual_stem = proof_manual_rel.stem
        if proof_manual_stem.endswith("_proof_manual"):
            goal_check_rel = proof_manual_rel.with_name(
                proof_manual_stem[: -len("_proof_manual")] + "_goal_check.v"
            )
        else:
            config = infer_case_config(main_root, formal_manual.parent)
            goal_check_rel = Path(config["check_file"])
        parent_check = run_coqc_check(
            workspace_root=main_root,
            build_workspace=run_builds_root(run_root) / round_id / "parent" / "src",
            target_file=goal_check_rel,
            target_kind="check",
            source_goal_version=str(base["source_goal_version"]),
            timeout_seconds=coq_timeout_seconds,
            overlays={proof_manual_rel: merged_manual, formal_case_lib_rel: proving_merged_lib},
        )
        if parent_check.get("status") != "passed":
            ready = False
            errors.append("proving_merged candidate failed parent full check")

    result = {
        "schema_version": "qcp-vc-proving-proving-merged-result/v2",
        "status": "passed" if ready else "failed",
        "source_goal_version": base.get("source_goal_version"),
        "candidate": {
            "proof_manual": str(merged_manual),
            "proving_merged_lib": str(proving_merged_lib),
            "proof_manual_sha256": _sha256(merged_manual),
            "proving_merged_lib_sha256": _sha256(proving_merged_lib),
            "formal_proof_manual_relative": proof_manual_rel.as_posix(),
            "formal_case_lib_relative": formal_case_lib_rel.as_posix(),
        },
        "groups": group_summaries,
        "added_declarations": _compact_declarations(added_declarations),
        "parent_check": _compact_check(parent_check),
        "forbidden_lemma_findings": forbidden,
        "blockers": blockers,
        "errors": errors,
    }
    write_json(report_directory / "proving_merged_result.json", result)
    return result
