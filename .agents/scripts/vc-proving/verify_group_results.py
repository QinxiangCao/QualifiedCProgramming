#!/usr/bin/env python3
"""Verify compact group results and build a deterministic proving_merged candidate."""

# ruff: noqa: E402 -- internal sibling modules are resolved from this script directory.

from __future__ import annotations

import json
import os
import re
import sys
from collections.abc import Collection
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from coq_tooling import run_coqc_check
from file_integrity import sha256_file as _sha256
from group_plan_utils import (
    group_aggressive_split_goal_names,
    group_witness_names,
)
from path_utils import (
    fixed_path_under,
    path_is_link_like,
    run_builds_root,
    slug,
    write_bytes,
    write_json,
)
from prepare_group_workers import (
    dispatch_order_for_entries,
    resolve_group_workers_manifest,
)
from proof_manual_utils import (
    HELPER_DECL_KINDS,
    block_has_incomplete_proof,
    coq_token_digest,
    declaration_block_digest,
    ensure_unique_lemma_names,
    forbidden_top_level_declarations,
    helper_namespace_for_group_id,
    incomplete_proof_markers,
    is_exact_declaration_line_range,
    lemma_by_name,
    lemma_proof_parts,
    lemma_statement_hash,
    markdown_table_cells,
    mask_coq_strings,
    merge_group_worker_libs,
    normalize_reuse_decision,
    parse_lib_declarations,
    parse_manual_file,
    partition_manual_lemmas,
    proof_mode_errors,
    rewrite_coq_identifiers,
    rollback_control_commands,
    strip_coq_comments,
    top_level_commands,
    unsafe_assumption_declarations,
    unsafe_typing_commands,
)
from public_helper_utils import (
    allowed_public_helper_blocks,
    round_public_helper_snapshot_path,
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
    "logic_equiv_coq_prop_andp_sepcon",
    "derivable1_sepcon_assoc1",
    "derivable1_sepcon_assoc2",
    "derivable1_orp_assoc1",
    "derivable1_andp_assoc",
    "provable_sepcon_assoc",
    "provable_sepcon_assoc1",
    "provable_sepcon_assoc2",
    "provable_orp_assoc",
    "provable_andp_assoc",
)

FORBIDDEN_TACTICS = (
    "entailer!",
    "pre_process",
)

FORBIDDEN_TOKENS = FORBIDDEN_LEMMAS + FORBIDDEN_TACTICS


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise SystemExit(f"JSON file must contain an object: {path}")
    return payload


def _seed_digests(base: dict[str, Any]) -> dict[str, str | None]:
    seed = base.get("seed_sha256")
    if not isinstance(seed, dict) or set(seed) != {
        "proof_manual",
        "formal_case_lib",
    }:
        raise SystemExit("base manifest seed_sha256 is invalid")
    result: dict[str, str | None] = {}
    for key in ("proof_manual", "formal_case_lib"):
        value = seed.get(key)
        if value is None:
            result[key] = None
        elif isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value):
            result[key] = value
        else:
            raise SystemExit(
                f"base manifest seed_sha256.{key} must be sha256 or null"
            )
    return result


def _seed_artifact_error(
    path: Path, digest: str | None, *, label: str
) -> str | None:
    if digest is None:
        return (
            f"{label} appeared after vc-proving preparation"
            if os.path.lexists(path)
            else None
        )
    if path_is_link_like(path) or not path.is_file() or _sha256(path) != digest:
        return f"{label} changed after vc-proving preparation"
    return None


def _read_utf8_exact(path: Path) -> str:
    """Read UTF-8 without universal-newline translation."""

    return path.read_bytes().decode("utf-8")


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
        parts.append(block)
    return "".join(parts)


def _manual_write_boundary_errors(
    *,
    group_id: str,
    seed_prelude: str,
    seed_lemmas: list[dict[str, Any]],
    candidate_prelude: str,
    candidate_lemmas: list[dict[str, Any]],
    editable: set[str],
) -> list[str]:
    """Keep proof ownership strict while ignoring formatting-only changes."""

    errors: list[str] = []
    if coq_token_digest(candidate_prelude) != coq_token_digest(seed_prelude):
        errors.append(
            f"{group_id}: protected manual prelude tokens changed"
        )
    seed_names = [str(item["name"]) for item in seed_lemmas]
    candidate_names = [str(item["name"]) for item in candidate_lemmas]
    if candidate_names != seed_names:
        mismatch = next(
            (
                index
                for index, (expected, actual) in enumerate(
                    zip(seed_names, candidate_names, strict=False)
                )
                if expected != actual
            ),
            min(len(seed_names), len(candidate_names)),
        )
        expected = seed_names[mismatch] if mismatch < len(seed_names) else "<EOF>"
        actual = (
            candidate_names[mismatch] if mismatch < len(candidate_names) else "<EOF>"
        )
        errors.append(
            f"{group_id}: copied manual declaration order differs at index "
            f"{mismatch}: expected `{expected}`, found `{actual}`"
        )

    candidate_map = lemma_by_name(candidate_lemmas)
    for seed_lemma in seed_lemmas:
        name = str(seed_lemma["name"])
        candidate = candidate_map.get(name)
        if candidate is None:
            continue
        seed_block = str(seed_lemma["block"])
        candidate_block = str(candidate["block"])
        if name not in editable:
            if coq_token_digest(candidate_block) != coq_token_digest(seed_block):
                errors.append(
                    f"{group_id}: protected unassigned block `{name}` tokens changed"
                )
            continue
        try:
            seed_statement, _seed_proof, seed_trailing = lemma_proof_parts(seed_block)
            (
                candidate_statement,
                _candidate_proof,
                candidate_trailing,
            ) = lemma_proof_parts(candidate_block)
        except ValueError as exc:
            errors.append(
                f"{group_id}: editable block `{name}` cannot be parsed: {exc}"
            )
            continue
        if coq_token_digest(candidate_statement) != coq_token_digest(seed_statement):
            errors.append(
                f"{group_id}: protected statement of editable block `{name}` changed"
            )
        if coq_token_digest(candidate_trailing) != coq_token_digest(seed_trailing):
            errors.append(
                f"{group_id}: protected tokens after editable block `{name}` changed"
            )
    return errors


def _forbidden_findings(path: Path) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    masked = mask_coq_strings(
        strip_coq_comments(path.read_text(encoding="utf-8"))
    )
    for line_number, line in enumerate(
        masked.splitlines(), start=1
    ):
        for lemma in FORBIDDEN_TOKENS:
            if re.search(
                rf"(?<![A-Za-z0-9_']){re.escape(lemma)}(?![A-Za-z0-9_'])", line
            ):
                findings.append(
                    {"path": str(path), "line": line_number, "lemma": lemma}
                )
    return findings


def _proving_merged_topology_errors(
    directory: Path,
    expected: dict[str, Path],
    *,
    require_present: bool,
) -> list[str]:
    errors: list[str] = []
    expected_paths = set(expected.values())
    if len(expected_paths) != len(expected):
        errors.append("proving_merged candidate roles collide on one path")
    try:
        children = list(directory.iterdir())
    except OSError as exc:
        return [f"cannot inspect proving_merged candidate directory: {exc}"]
    for child in children:
        if child not in expected_paths:
            errors.append(f"proving_merged contains an unexpected entry: {child}")
        elif path_is_link_like(child) or not child.is_file():
            errors.append(
                f"proving_merged candidate must be a fixed regular file: {child}"
            )
    if require_present:
        for label, path in expected.items():
            if (
                not os.path.lexists(path)
                or path_is_link_like(path)
                or not path.is_file()
            ):
                errors.append(f"proving_merged {label} candidate is missing: {path}")
    return errors


def _group_layout_errors(
    group: dict[str, Any], groups_directory: Path, report_directory: Path
) -> list[str]:
    group_id = str(group.get("id") or "")
    directory = Path(str(group.get("directory", ""))).resolve()
    manual = Path(str(group.get("proof_manual", ""))).resolve()
    raw_worker_lib = group.get("group_worker_lib")
    worker_lib = (
        Path(raw_worker_lib).resolve()
        if isinstance(raw_worker_lib, str) and raw_worker_lib
        else None
    )
    errors: list[str] = []
    expected_name = f"group_{int(group.get('index', -1)):02d}__{slug(group_id)}"
    if directory.parent != groups_directory or directory.name != expected_name:
        errors.append(f"{group_id}: invalid fixed group directory")
    if manual.parent != directory or (
        worker_lib is not None and worker_lib.parent != directory
    ):
        expected = (
            "copied manual and group_worker_lib"
            if worker_lib is not None
            else "copied manual"
        )
        errors.append(
            f"{group_id}: {expected} must be direct children of the group directory"
        )
    expected_files = {manual.name}
    if worker_lib is not None:
        expected_files.add(worker_lib.name)
    actual_files = (
        {path.name for path in directory.iterdir()} if directory.is_dir() else set()
    )
    if actual_files != expected_files:
        errors.append(
            f"{group_id}: group directory contains files outside its sealed formal candidates"
        )
    expected_report = report_directory / "groups" / directory.name
    if Path(str(group.get("report_directory", ""))).resolve() != expected_report:
        errors.append(f"{group_id}: invalid group report directory")
    for name in (
        "group_worker_input.md",
        "group_worker_report.json",
    ):
        if not (expected_report / name).is_file():
            errors.append(f"{group_id}: missing {name}")
    proof_reuse = expected_report / "proof_reuse.md"
    if group.get("proof_reuse") or group.get("proof_reuse_sha256"):
        if Path(str(group.get("proof_reuse") or "")).resolve() != proof_reuse:
            errors.append(f"{group_id}: invalid proof reuse hint path")
        elif not proof_reuse.is_file() or _sha256(proof_reuse) != group.get(
            "proof_reuse_sha256"
        ):
            errors.append(f"{group_id}: proof reuse hint changed after preparation")
        sources = group.get("proof_reuse_sources", [])
        if not isinstance(sources, list) or not all(
            isinstance(item, dict) for item in sources
        ):
            errors.append(f"{group_id}: invalid proof reuse source records")
        else:
            run_root = groups_directory.parent.parent
            source_paths: set[Path] = set()
            for item in sources:
                source = Path(str(item.get("path") or "")).expanduser().resolve()
                source_paths.add(source)
                if not _is_relative_to(source, run_root):
                    errors.append(
                        f"{group_id}: proof reuse source is outside the current run"
                    )
                elif not source.is_file() or _sha256(source) != item.get("sha256"):
                    errors.append(
                        f"{group_id}: proof reuse source changed after preparation"
                    )
            try:
                referenced_paths = {
                    Path(row["previous file"]).expanduser().resolve()
                    for row in _reuse_table_rows(proof_reuse)
                    if normalize_reuse_decision(row["decision"]) != "from scratch"
                }
            except (OSError, UnicodeDecodeError, ValueError) as exc:
                errors.append(f"{group_id}: invalid proof reuse hint: {exc}")
            else:
                if referenced_paths != source_paths:
                    errors.append(
                        f"{group_id}: proof reuse hint paths do not exactly match sealed source records"
                    )
    elif proof_reuse.exists():
        errors.append(
            f"{group_id}: unexpected proof reuse hint without a failed previous round"
        )
    elif group.get("proof_reuse_sources"):
        errors.append(f"{group_id}: proof reuse sources exist without a hint")
    run_root = groups_directory.parent.parent
    expected_public = round_public_helper_snapshot_path(
        run_root, groups_directory.parent.name
    )
    if (
        Path(str(group.get("public_helper_lemma_lib") or "")).resolve()
        != expected_public
    ):
        errors.append(f"{group_id}: invalid public helper candidate pool path")
    elif not expected_public.is_file():
        errors.append(f"{group_id}: public helper candidate pool is missing")
    elif _sha256(expected_public) != str(
        group.get("public_helper_lemma_lib_sha256") or ""
    ):
        errors.append(f"{group_id}: public helper candidate snapshot changed")
    return errors


def _direct_helper_hint_blocks(group: dict[str, Any]) -> dict[str, set[str]]:
    """Load exact helper blocks approved by this group's accepted reuse hint."""

    hint = Path(str(group.get("proof_reuse") or ""))
    if not group.get("proof_reuse") or not hint.is_file():
        return {}
    allowed: dict[str, set[str]] = {}
    for row in _reuse_table_rows(hint):
        label = row["current goal"]
        if (
            not label.startswith("helper:")
            or normalize_reuse_decision(row["decision"]) != "direct copy"
        ):
            continue
        helper_name = label.split(":", 1)[1]
        line_match = re.fullmatch(r"(\d+)(?:\s*-\s*(\d+))?", row["lines"])
        source = Path(row["previous file"]).expanduser().resolve()
        if line_match is None or not source.is_file():
            continue
        start = int(line_match.group(1))
        end = int(line_match.group(2) or start)
        declaration = next(
            (
                item
                for item in parse_lib_declarations(_read_utf8_exact(source))
                if str(item.get("name")) == helper_name
                and is_exact_declaration_line_range(
                    start,
                    end,
                    declaration_start=int(item.get("start_line", 0)),
                    declaration_end=int(item.get("end_line", 0)),
                )
            ),
            None,
        )
        if declaration is not None:
            allowed.setdefault(helper_name, set()).add(
                declaration_block_digest(str(declaration["block"]))
            )
    return allowed


def _allowed_helper_blocks_for_group(
    group: dict[str, Any], run_root: Path
) -> dict[str, set[str]]:
    del run_root
    snapshot = Path(str(group.get("public_helper_lemma_lib") or ""))
    if not snapshot.is_file() or _sha256(snapshot) != str(
        group.get("public_helper_lemma_lib_sha256") or ""
    ):
        raise ValueError("public helper candidate snapshot changed")
    allowed = allowed_public_helper_blocks(snapshot)
    for name, digests in _direct_helper_hint_blocks(group).items():
        allowed.setdefault(name, set()).update(digests)
    return allowed


def _compact_declarations(items: list[dict[str, str]]) -> list[dict[str, str]]:
    keys = (
        "name",
        "kind",
        "group_id",
        "statement_hash",
        "helper_namespace_suffix",
        "helper_origin",
    )
    return [{key: str(item[key]) for key in keys if key in item} for item in items]


def _candidate_errors_are_worker_recoverable(errors: list[str]) -> bool:
    controller_owned_markers = (
        "invalid fixed group directory",
        "invalid group report directory",
        "missing group_worker_input.md",
        "missing group_worker_report.json",
        "proof reuse",
        "public/reuse helper candidates",
        "assigned witnesses must be non-empty and unique",
        "helper namespace mismatch",
    )
    return bool(errors) and not any(
        marker in error for marker in controller_owned_markers for error in errors
    )


def _manifest_context(
    manifest_path: Path,
    main_root: Path,
    *,
    seed_root: Path | None = None,
    expected_run_root: Path | None = None,
    expected_round: str | None = None,
) -> dict[str, Any]:
    main_root = main_root.expanduser().resolve()
    manifest_path = fixed_path_under(
        manifest_path,
        main_root,
        label="group workers manifest",
    )
    try:
        report_relative = manifest_path.relative_to(main_root / "reports")
    except ValueError as exc:
        raise SystemExit(
            "group_workers_manifest is outside the fixed report root"
        ) from exc
    if (
        len(report_relative.parts) != 4
        or report_relative.parts[1] != "rounds"
        or report_relative.parts[3] != "group_workers_manifest.json"
    ):
        raise SystemExit("group_workers_manifest does not use the fixed report layout")
    run_id, _rounds, report_round, _name = report_relative.parts
    manifest = resolve_group_workers_manifest(
        manifest_path,
        main_root=main_root,
        seed_root=seed_root,
        expected_run_root=expected_run_root,
        expected_round=expected_round,
    )
    if (
        not isinstance(manifest.get("groups"), list)
        or not all(isinstance(item, dict) for item in manifest["groups"])
    ):
        raise SystemExit("group_workers_manifest groups must be an object list")
    group_ids = [str(item.get("id") or "") for item in manifest["groups"]]
    if any("depends_on" in item for item in manifest["groups"]):
        raise SystemExit(
            "group_workers_manifest group contains unsupported field: depends_on"
        )
    if manifest.get("order") != group_ids:
        raise SystemExit(
            "group_workers_manifest order must match deterministic accepted-plan order"
        )
    dispatch_order = manifest.get("dispatch_order")
    if (
        not isinstance(dispatch_order, list)
        or len(dispatch_order) != len(group_ids)
        or {str(item) for item in dispatch_order} != set(group_ids)
    ):
        raise SystemExit(
            "group_workers_manifest dispatch_order must be an exact group-id permutation"
        )
    if [str(item) for item in dispatch_order] != dispatch_order_for_entries(
        manifest["groups"]
    ):
        raise SystemExit(
            "group_workers_manifest dispatch_order does not match the deterministic no-reuse/difficulty priority"
        )
    round_id = str(manifest.get("round") or "")
    if not round_id or report_round != slug(round_id):
        raise SystemExit(
            "group_workers_manifest round does not match its fixed report directory"
        )
    run_root = fixed_path_under(
        main_root / "verification_runs" / run_id,
        main_root,
        label="run root",
    )
    if expected_run_root is not None:
        expected_run = fixed_path_under(
            expected_run_root,
            main_root,
            label="expected current run root",
        )
        if run_root != expected_run:
            raise SystemExit(
                "group_workers_manifest is not bound to the expected current run"
            )
    if run_root.parent != main_root / "verification_runs" or not run_root.is_dir():
        raise SystemExit("group_workers_manifest run root is missing or invalid")
    expected_public = round_public_helper_snapshot_path(run_root, round_id)
    if (
        Path(str(manifest.get("public_helper_lemma_lib") or "")).resolve()
        != expected_public
    ):
        raise SystemExit(
            "group_workers_manifest public_helper_lemma_lib does not use the fixed round snapshot path"
        )
    expected_public_sha256 = str(manifest.get("public_helper_lemma_lib_sha256") or "")
    if (
        not expected_public.is_file()
        or not expected_public_sha256
        or _sha256(expected_public) != expected_public_sha256
    ):
        raise SystemExit("group_workers_manifest public helper snapshot changed")
    if any(
        Path(str(group.get("public_helper_lemma_lib") or "")).resolve()
        != expected_public
        or str(group.get("public_helper_lemma_lib_sha256") or "")
        != expected_public_sha256
        for group in manifest["groups"]
    ):
        raise SystemExit(
            "group_workers_manifest groups do not share its frozen public helper snapshot"
        )
    vc_directory = fixed_path_under(
        run_root / round_id,
        run_root,
        label="vc-proving round directory",
    )
    expected_base = fixed_path_under(
        vc_directory / "base_manifest.json",
        vc_directory,
        label="base manifest",
    )
    base_path = fixed_path_under(
        Path(str(manifest.get("base_manifest") or "")),
        vc_directory,
        label="declared base manifest",
    )
    if base_path != expected_base:
        raise SystemExit(
            "group_workers_manifest base_manifest does not use the fixed vc-proving path"
    )
    base = _load_json(base_path)
    if set(base) != {
        "source_goal_version",
        "proof_manual",
        "formal_case_lib",
        "seed_sha256",
    }:
        raise SystemExit("base manifest contains unsupported or missing fields")
    if vc_directory.name != round_id:
        raise SystemExit("base manifest round mismatch")
    if manifest.get("source_goal_version") != base.get("source_goal_version"):
        raise SystemExit("group_workers_manifest source_goal_version is stale")
    proof_manual_rel = Path(str(base.get("proof_manual") or ""))
    formal_case_lib_rel = Path(str(base.get("formal_case_lib") or ""))
    for label, relative in (
        ("proof_manual", proof_manual_rel),
        ("formal_case_lib", formal_case_lib_rel),
    ):
        if (
            relative.is_absolute()
            or ".." in relative.parts
            or not relative.parts
            or relative.parts[0] != "Rocq"
        ):
            raise SystemExit(
                f"base manifest {label} must be a formal repository-relative path"
            )
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
    seed_lemmas: list[dict[str, Any]],
    seed_map: dict[str, dict[str, Any]],
    seed_lib_text: str | None,
    groups_directory: Path,
    report_directory: Path,
    require_complete: bool,
    forbidden_modules: Collection[str],
) -> dict[str, Any]:
    group_id = str(group.get("id") or "")
    raw_witnesses = group.get("witnesses")
    witnesses = (
        raw_witnesses
        if isinstance(raw_witnesses, list)
        and all(isinstance(item, dict) for item in raw_witnesses)
        else []
    )
    assigned = group_witness_names(group)
    aggressive_split_goals = group_aggressive_split_goal_names(group)
    editable = set(assigned) | set(aggressive_split_goals)
    errors = _group_layout_errors(group, groups_directory, report_directory)
    if not witnesses or not assigned or len(assigned) != len(set(assigned)):
        errors.append(f"{group_id}: assigned witnesses must be non-empty and unique")
    try:
        expected_namespace = helper_namespace_for_group_id(group_id)
    except ValueError as exc:
        errors.append(str(exc))
        expected_namespace = {}
    if group.get("helper_namespace") != expected_namespace:
        errors.append(f"{group_id}: helper namespace mismatch")
    group_manual = Path(str(group.get("proof_manual") or ""))
    raw_group_worker_lib = group.get("group_worker_lib")
    group_worker_lib = (
        Path(raw_group_worker_lib)
        if isinstance(raw_group_worker_lib, str) and raw_group_worker_lib
        else None
    )
    if seed_lib_text is None and group.get("helpers"):
        errors.append(
            f"{group_id}: planned helpers require a formal_case_lib candidate"
        )
    if (seed_lib_text is None) != (group_worker_lib is None):
        errors.append(
            f"{group_id}: group_worker_lib presence does not match the sealed formal_case_lib seed"
        )
    group_map: dict[str, dict[str, Any]] = {}
    group_lemmas: list[dict[str, Any]] = []
    group_prelude = ""
    group_manual_parsed = False
    group_manual_text = ""
    group_worker_lib_text: str | None = None
    try:
        group_manual_text = _read_utf8_exact(group_manual)
        group_prelude, group_lemmas = parse_manual_file(group_manual_text)
        ensure_unique_lemma_names(group_lemmas)
        group_map = lemma_by_name(group_lemmas)
        group_manual_parsed = True
    except (OSError, ValueError) as exc:
        errors.append(f"{group_id}: copied manual cannot be parsed: {exc}")
    if group_manual_parsed:
        errors.extend(
            _manual_write_boundary_errors(
                group_id=group_id,
                seed_prelude=seed_prelude,
                seed_lemmas=seed_lemmas,
                candidate_prelude=group_prelude,
                candidate_lemmas=group_lemmas,
                editable=editable,
            )
        )
    if set(group_map) == set(seed_map):
        for witness in witnesses:
            name = str(witness["name"])
            seed_lemma = seed_map.get(name)
            candidate = group_map.get(name)
            if seed_lemma is None or candidate is None:
                errors.append(f"{group_id}: assigned witness `{name}` is missing")
            elif lemma_statement_hash(seed_lemma) != lemma_statement_hash(candidate):
                errors.append(f"{group_id}: witness statement changed for `{name}`")
            elif any(
                item["kind"] == "Admitted"
                for item in incomplete_proof_markers(str(candidate["block"]))
            ):
                errors.append(f"{group_id}: witness `{name}` contains Admitted")
            elif require_complete and block_has_incomplete_proof(
                str(candidate["block"])
            ):
                errors.append(f"{group_id}: witness `{name}` contains Admitted/Abort")
            else:
                commands = top_level_commands(str(candidate["block"]))
                if (
                    len(commands) != 1
                    or commands[0].get("kind")
                    not in {
                        "Lemma",
                        "Theorem",
                        "Proposition",
                        "Corollary",
                        "Example",
                        "Fact",
                        "Remark",
                    }
                    or commands[0].get("name") != name
                ):
                    errors.append(
                        f"{group_id}: witness `{name}` contains an extra top-level command"
                    )
                if require_complete:
                    for route_error in proof_mode_errors(
                        str(candidate["block"]),
                        str(witness.get("proof_mode") or ""),
                    ):
                        errors.append(f"{group_id}: witness `{name}` {route_error}")
            if witness.get("proof_mode") != "aggressive_pre_process":
                continue
            for split_goal in witness.get("split_goals", []):
                split_name = str(split_goal["name"])
                seed_split = seed_map.get(split_name)
                candidate_split = group_map.get(split_name)
                if seed_split is None or candidate_split is None:
                    errors.append(
                        f"{group_id}: aggressive split goal `{split_name}` is missing"
                    )
                elif lemma_statement_hash(seed_split) != lemma_statement_hash(
                    candidate_split
                ):
                    errors.append(
                        f"{group_id}: split-goal statement changed for `{split_name}`"
                    )
                elif any(
                    item["kind"] == "Admitted"
                    for item in incomplete_proof_markers(
                        str(candidate_split["block"])
                    )
                ):
                    errors.append(
                        f"{group_id}: aggressive split goal `{split_name}` contains Admitted"
                    )
                elif require_complete and block_has_incomplete_proof(
                    str(candidate_split["block"])
                ):
                    errors.append(
                        f"{group_id}: aggressive split goal `{split_name}` contains Admitted/Abort"
                    )
                else:
                    commands = top_level_commands(str(candidate_split["block"]))
                    if len(commands) != 1 or commands[0].get("name") != split_name:
                        errors.append(
                            f"{group_id}: split goal `{split_name}` contains an extra top-level command"
                        )
    manual_forbidden = (
        unsafe_typing_commands(group_manual_text)
        + rollback_control_commands(group_manual_text)
        + unsafe_assumption_declarations(group_manual_text)
        + forbidden_top_level_declarations(
            group_manual_text,
            {
                "Definition",
                "Fixpoint",
                "CoFixpoint",
                "Inductive",
                "CoInductive",
                "Notation",
            },
        )
    )
    if manual_forbidden:
        errors.append(
            f"{group_id}: copied manual contains forbidden top-level declarations"
        )
    if group_worker_lib is not None and seed_lib_text is not None:
        try:
            group_worker_lib_text = _read_utf8_exact(group_worker_lib)
        except OSError as exc:
            errors.append(f"{group_id}: group_worker_lib cannot be read: {exc}")
        else:
            try:
                allowed_helper_blocks = _allowed_helper_blocks_for_group(
                    group, groups_directory.parent.parent
                )
            except (OSError, ValueError) as exc:
                errors.append(
                    f"{group_id}: public/reuse helper candidates cannot be validated: {exc}"
                )
                allowed_helper_blocks = {}
            _merged, _added, _renames, lib_errors = merge_group_worker_libs(
                seed_lib_text,
                [(group_id, group_worker_lib_text, expected_namespace)],
                allowed_public_helpers_by_group={group_id: allowed_helper_blocks},
                forbidden_modules=forbidden_modules,
            )
            errors.extend(
                f"{group_id}: group_worker_lib contract: {error}"
                for error in lib_errors
            )
    forbidden: list[dict[str, Any]] = []
    candidate_paths = [group_manual]
    if group_worker_lib is not None:
        candidate_paths.append(group_worker_lib)
    for path in candidate_paths:
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


def validate_group_for_acceptance_result(
    manifest_path: Path,
    *,
    group_id: str,
    main_root: Path,
    expected_proof_manual: str,
    expected_formal_case_lib: str,
    require_complete: bool = True,
    seed_root: Path | None = None,
    forbidden_modules: Collection[str] = (),
    expected_run_root: Path | None = None,
    expected_round: str | None = None,
) -> dict[str, Any]:
    """Validate one group copy and classify candidate-local repairability."""

    main_root = main_root.expanduser().resolve()
    context = _manifest_context(
        manifest_path,
        main_root,
        seed_root=seed_root,
        expected_run_root=expected_run_root,
        expected_round=expected_round,
    )
    base = context["base"]
    errors: list[str] = []
    if (
        base.get("proof_manual") != expected_proof_manual
        or base.get("formal_case_lib") != expected_formal_case_lib
    ):
        errors.append(
            "vc-proving base manifest does not match current target formal paths"
        )
    seed_owner = (
        seed_root.expanduser().resolve() if seed_root is not None else main_root
    )
    formal_manual = seed_owner / context["proof_manual_rel"]
    formal_case_lib = seed_owner / context["formal_case_lib_rel"]
    seed = _seed_digests(base)
    manual_seed_error = _seed_artifact_error(
        formal_manual, seed["proof_manual"], label="formal proof manual"
    )
    lib_seed_error = _seed_artifact_error(
        formal_case_lib, seed["formal_case_lib"], label="formal_case_lib"
    )
    if manual_seed_error:
        errors.append(manual_seed_error)
    if lib_seed_error:
        errors.append(lib_seed_error)
    if seed["proof_manual"] is None:
        errors.append("group validation requires a sealed proof manual")
    if errors:
        return {"errors": errors, "recoverable": False}
    seed_prelude, seed_lemmas = parse_manual_file(_read_utf8_exact(formal_manual))
    ensure_unique_lemma_names(seed_lemmas)
    seed_map = lemma_by_name(seed_lemmas)
    group = next(
        (
            item
            for item in context["manifest"].get("groups", [])
            if str(item.get("id")) == group_id
        ),
        None,
    )
    if not isinstance(group, dict):
        return {
            "errors": [f"{group_id}: group missing from current manifest"],
            "recoverable": False,
        }
    result = _validate_group_candidate_content(
        group,
        seed_prelude=seed_prelude,
        seed_lemmas=seed_lemmas,
        seed_map=seed_map,
        seed_lib_text=(
            _read_utf8_exact(formal_case_lib)
            if seed["formal_case_lib"] is not None
            else None
        ),
        groups_directory=context["vc_directory"] / "groups",
        report_directory=context["report_directory"],
        require_complete=require_complete,
        forbidden_modules=forbidden_modules,
    )
    candidate_errors = [str(item) for item in result["errors"]]
    return {
        "errors": candidate_errors,
        "recoverable": _candidate_errors_are_worker_recoverable(candidate_errors),
    }


def _reuse_table_rows(path: Path) -> list[dict[str, str]]:
    rows: list[list[str]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not (stripped.startswith("|") and stripped.endswith("|")):
            continue
        rows.append(markdown_table_cells(stripped))
    header = ["current goal", "decision", "previous file", "lines", "reason"]
    header_index = next(
        (
            index
            for index, row in enumerate(rows)
            if [cell.lower() for cell in row] == header
        ),
        None,
    )
    if header_index is None:
        raise ValueError(f"proof reuse hint has no canonical table: {path}")
    result: list[dict[str, str]] = []
    for row in rows[header_index + 2 :]:
        if len(row) != len(header):
            raise ValueError(f"proof reuse hint row has the wrong width: {path}")
        result.append(dict(zip(header, row, strict=True)))
    return result


def _group_reuse_measurement(
    group: dict[str, Any],
    group_map: dict[str, dict[str, Any]],
    group_worker_lib_text: str = "",
) -> dict[str, Any]:
    hint_path = Path(str(group.get("proof_reuse") or ""))
    if not group.get("proof_reuse"):
        return {"enabled": False}
    unit_kinds: dict[str, str] = {}
    for witness in group.get("witnesses", []):
        if not isinstance(witness, dict):
            continue
        unit_kinds[str(witness.get("name") or "")] = "top-level"
        for split_goal in witness.get("split_goals", []):
            if isinstance(split_goal, dict):
                unit_kinds[str(split_goal.get("name") or "")] = "split-goal"
    for helper in group.get("helpers", []):
        if isinstance(helper, dict):
            unit_kinds[f"helper:{helper.get('name')}"] = "helper"
    rows = _reuse_table_rows(hint_path)
    decisions = {
        "direct_copy": 0,
        "partial_proof_idea_reuse": 0,
        "from_scratch": 0,
    }
    direct_exact = 0
    direct_reworked = 0
    exact_by_kind = {"top-level": 0, "split-goal": 0, "helper": 0}
    by_kind = {
        kind: {
            "hint_decisions": {
                "direct_copy": 0,
                "partial_proof_idea_reuse": 0,
                "from_scratch": 0,
            },
            "direct_copy_exact": 0,
            "direct_copy_reworked": 0,
        }
        for kind in ("top-level", "split-goal", "helper")
    }
    parsed_previous: dict[Path, list[dict[str, Any]]] = {}
    current_helpers = {
        str(item["name"]): item
        for item in parse_lib_declarations(group_worker_lib_text)
        if str(item["kind"]) in HELPER_DECL_KINDS
    }
    for row in rows:
        decision = normalize_reuse_decision(row["decision"])
        decision_key = decision.replace("-", "_").replace(" ", "_")
        name = row["current goal"]
        kind = unit_kinds.get(name, "top-level")
        if decision_key in decisions:
            decisions[decision_key] += 1
            by_kind[kind]["hint_decisions"][decision_key] += 1
        if decision != "direct copy":
            continue
        is_helper = name.startswith("helper:")
        helper_name = name.split(":", 1)[1] if is_helper else ""
        current = current_helpers.get(helper_name) if is_helper else group_map.get(name)
        line_match = re.fullmatch(r"(\d+)(?:\s*-\s*(\d+))?", row["lines"])
        previous_path = Path(row["previous file"]).expanduser().resolve()
        if current is None or line_match is None or not previous_path.is_file():
            direct_reworked += 1
            by_kind[kind]["direct_copy_reworked"] += 1
            continue
        start = int(line_match.group(1))
        end = int(line_match.group(2) or start)
        if previous_path not in parsed_previous:
            if is_helper:
                parsed_previous[previous_path] = parse_lib_declarations(
                    _read_utf8_exact(previous_path)
                )
            else:
                _prelude, previous_lemmas = parse_manual_file(
                    _read_utf8_exact(previous_path)
                )
                parsed_previous[previous_path] = previous_lemmas
        previous = next(
            (
                lemma
                for lemma in parsed_previous[previous_path]
                if is_exact_declaration_line_range(
                    start,
                    end,
                    declaration_start=int(lemma["start_line"]),
                    declaration_end=int(lemma["end_line"]),
                )
            ),
            None,
        )
        if previous is None:
            direct_reworked += 1
            by_kind[kind]["direct_copy_reworked"] += 1
            continue
        if is_helper:
            exact = declaration_block_digest(
                str(current["block"])
            ) == declaration_block_digest(str(previous["block"]))
        else:
            _current_statement, current_proof, _current_tail = lemma_proof_parts(
                current
            )
            _previous_statement, previous_proof, _previous_tail = lemma_proof_parts(
                previous
            )
            exact = coq_token_digest(current_proof) == coq_token_digest(previous_proof)
        if exact:
            direct_exact += 1
            exact_by_kind[kind] = exact_by_kind.get(kind, 0) + 1
            by_kind[kind]["direct_copy_exact"] += 1
        else:
            direct_reworked += 1
            by_kind[kind]["direct_copy_reworked"] += 1
    return {
        "enabled": True,
        "measurement": "proof-token-identity",
        "comparison_units": len(rows),
        "hint_decisions": decisions,
        "direct_copy_exact": direct_exact,
        "direct_copy_reworked": direct_reworked,
        "exact_by_kind": exact_by_kind,
        "by_kind": by_kind,
    }


def _merge_reuse_measurements(groups: list[dict[str, Any]]) -> dict[str, Any]:
    measurement_errors = [
        str(group["measurement_error"])
        for group in groups
        if group.get("measurement_error")
    ]
    enabled = [
        group
        for group in groups
        if group.get("enabled") and not group.get("measurement_error")
    ]
    if not enabled:
        return (
            {
                "error_count": len(measurement_errors),
                "first_error": measurement_errors[0],
            }
            if measurement_errors
            else {}
        )
    return {
        "by_kind": {
            kind: {
                "direct_copy": sum(
                    int(
                        group.get("by_kind", {})
                        .get(kind, {})
                        .get("hint_decisions", {})
                        .get("direct_copy", 0)
                    )
                    for group in enabled
                ),
                "partial_reuse": sum(
                    int(
                        group.get("by_kind", {})
                        .get(kind, {})
                        .get("hint_decisions", {})
                        .get("partial_proof_idea_reuse", 0)
                    )
                    for group in enabled
                ),
                "from_scratch": sum(
                    int(
                        group.get("by_kind", {})
                        .get(kind, {})
                        .get("hint_decisions", {})
                        .get("from_scratch", 0)
                    )
                    for group in enabled
                ),
                "exact": sum(
                    int(
                        group.get("by_kind", {})
                        .get(kind, {})
                        .get("direct_copy_exact", 0)
                    )
                    for group in enabled
                ),
                "reworked": sum(
                    int(
                        group.get("by_kind", {})
                        .get(kind, {})
                        .get("direct_copy_reworked", 0)
                    )
                    for group in enabled
                ),
            }
            for kind in ("top-level", "split-goal", "helper")
        },
        **(
            {
                "error_count": len(measurement_errors),
                "first_error": measurement_errors[0],
            }
            if measurement_errors
            else {}
        ),
    }


def verify_and_merge(
    manifest_path: Path,
    *,
    main_root: Path | None = None,
    coq_timeout_seconds: int | None = None,
    goal_check_file: Path | None = None,
    forbidden_modules: Collection[str] = (),
    expected_run_root: Path | None = None,
    expected_round: str | None = None,
) -> dict[str, Any]:
    # Preserve the caller's lexical path until ``_manifest_context`` checks
    # every component; resolving here would hide a symlinked report child.
    manifest_path = manifest_path.expanduser().absolute()
    if main_root is None:
        try:
            report_relative = manifest_path.parents[3]
        except IndexError as exc:
            raise SystemExit(
                "cannot infer main root from group_workers_manifest"
            ) from exc
        if report_relative.name != "reports":
            raise SystemExit(
                "--main-root is required for a manifest outside the fixed report root"
            )
        main_root = report_relative.parent
    main_root = main_root.expanduser().resolve()
    context = _manifest_context(
        manifest_path,
        main_root,
        expected_run_root=expected_run_root,
        expected_round=expected_round,
    )
    base = context["base"]
    vc_directory = context["vc_directory"]
    run_root = context["run_root"]
    round_id = context["round_id"]
    report_directory = context["report_directory"]
    proof_manual_rel = context["proof_manual_rel"]
    formal_case_lib_rel = context["formal_case_lib_rel"]
    formal_manual = main_root / proof_manual_rel
    formal_case_lib = main_root / formal_case_lib_rel
    seed = _seed_digests(base)
    for error in (
        _seed_artifact_error(
            formal_manual, seed["proof_manual"], label="formal proof manual"
        ),
        _seed_artifact_error(
            formal_case_lib, seed["formal_case_lib"], label="formal_case_lib"
        ),
    ):
        if error:
            raise SystemExit(error)
    seed_manual_text = (
        _read_utf8_exact(formal_manual) if seed["proof_manual"] is not None else None
    )
    seed_lib_text = (
        _read_utf8_exact(formal_case_lib)
        if seed["formal_case_lib"] is not None
        else None
    )
    if seed_manual_text is not None:
        seed_prelude, seed_lemmas = parse_manual_file(seed_manual_text)
        ensure_unique_lemma_names(seed_lemmas)
    else:
        seed_prelude, seed_lemmas = "", []
    seed_map = lemma_by_name(seed_lemmas)
    target_witnesses = [
        str(item["name"]) for item in partition_manual_lemmas(seed_lemmas)[0]
    ]

    replacements: dict[str, str] = {}
    solved: list[str] = []
    errors: list[str] = []
    group_lib_texts: list[tuple[str, str, dict[str, Any]]] = []
    valid_group_contents: dict[str, dict[str, Any]] = {}
    allowed_helper_blocks_by_group: dict[str, dict[str, set[str]]] = {}
    reuse_measurements: list[dict[str, Any]] = []
    groups_directory = vc_directory / "groups"

    for group in context["manifest"]["groups"]:
        group_id = str(group["id"])
        assigned = group_witness_names(group)
        content = _validate_group_candidate_content(
            group,
            seed_prelude=seed_prelude,
            seed_lemmas=seed_lemmas,
            seed_map=seed_map,
            seed_lib_text=seed_lib_text,
            groups_directory=groups_directory,
            report_directory=report_directory,
            require_complete=True,
            forbidden_modules=forbidden_modules,
        )
        group_errors = [str(item) for item in content["errors"]]
        report_path = Path(str(group["report_directory"])) / "group_worker_report.json"
        try:
            report = _load_json(report_path)
        except (OSError, json.JSONDecodeError, SystemExit) as exc:
            report = {}
            group_errors.append(f"{group_id}: invalid group report: {exc}")
        extra_report_fields = set(report) - {"status"}
        if extra_report_fields:
            group_errors.append(
                f"{group_id}: unsupported group report fields: {sorted(extra_report_fields)}"
            )
        if report.get("status") != "completed":
            group_errors.append(f"{group_id}: group report status must be completed")
        try:
            group_reuse = _group_reuse_measurement(
                group,
                content["group_map"],
                str(content.get("group_worker_lib_text") or ""),
            )
        except (OSError, ValueError) as exc:
            group_reuse = {"enabled": False, "measurement_error": str(exc)}
            group_errors.append(f"{group_id}: proof reuse measurement failed: {exc}")
        reuse_index = len(reuse_measurements)
        reuse_measurements.append(group_reuse)
        if group_errors:
            errors.extend(group_errors)
            continue

        group_map = content["group_map"]
        for name in [*assigned, *group_aggressive_split_goal_names(group)]:
            replacements[name] = str(group_map[name]["block"])
        solved.extend(assigned)
        if seed_lib_text is not None:
            group_lib_texts.append(
                (
                    group_id,
                    str(content["group_worker_lib_text"]),
                    content["expected_namespace"],
                )
            )
            allowed_helper_blocks_by_group[group_id] = (
                _allowed_helper_blocks_for_group(group, run_root)
            )
        valid_group_contents[group_id] = {
            "group": group,
            "content": content,
            "reuse_index": reuse_index,
        }

    if seed_lib_text is not None:
        (
            merged_lib_text,
            added_declarations,
            helper_renames_by_group,
            lib_errors,
        ) = merge_group_worker_libs(
            seed_lib_text,
            group_lib_texts,
            allowed_public_helpers_by_group=allowed_helper_blocks_by_group,
            forbidden_modules=forbidden_modules,
        )
        errors.extend(f"group_worker_lib merge: {error}" for error in lib_errors)
    else:
        merged_lib_text = None
        added_declarations = []
        helper_renames_by_group = {}
    for group_id, renames in helper_renames_by_group.items():
        group_record = valid_group_contents.get(group_id)
        if group_record is None:
            errors.append(
                f"group_worker_lib merge: helper rename references unknown group `{group_id}`"
            )
            continue
        group = group_record["group"]
        content = group_record["content"]
        group_map = content["group_map"]
        for name in [
            *group_witness_names(group),
            *group_aggressive_split_goal_names(group),
        ]:
            replacements[name] = rewrite_coq_identifiers(
                str(group_map[name]["block"]),
                renames,
            )

        # Recompute reuse statistics from the transformed candidate bytes.
        # A direct-copy proof/helper that needed an identifier rewrite is a
        # reworked unit in the final merge, even though the sealed group input
        # was exact before collision resolution.
        transformed_group_map = {
            name: {
                **lemma,
                "block": rewrite_coq_identifiers(str(lemma["block"]), renames),
            }
            for name, lemma in group_map.items()
        }
        group_lib_text = str(content["group_worker_lib_text"])
        transformed_group_lib_text = (
            seed_lib_text
            + rewrite_coq_identifiers(
                group_lib_text[len(seed_lib_text) :],
                renames,
            )
            if group_lib_text.startswith(seed_lib_text)
            else group_lib_text
        )
        try:
            transformed_reuse = _group_reuse_measurement(
                group,
                transformed_group_map,
                transformed_group_lib_text,
            )
        except (OSError, ValueError) as exc:
            transformed_reuse = {
                "enabled": False,
                "measurement_error": str(exc),
            }
            errors.append(
                f"{group_id}: transformed proof reuse measurement failed: {exc}"
            )
        reuse_measurements[int(group_record["reuse_index"])] = transformed_reuse

    merged_manual_text = (
        _replace_blocks(seed_manual_text, replacements)
        if seed_manual_text is not None
        else None
    )
    # The parent merge is a formal-output boundary.  Validate the lexical path
    # immediately before writing so a post-preparation child symlink cannot
    # redirect candidate files outside the run.
    proving_merged_directory = fixed_path_under(
        vc_directory / "proving_merged",
        run_root,
        label="proving_merged directory",
    )
    proving_merged_directory.mkdir(parents=True, exist_ok=True)
    manual_candidate = proving_merged_directory / formal_manual.name
    lib_candidate = proving_merged_directory / formal_case_lib.name
    expected_candidates = {
        label: path
        for label, path, present in (
            ("manual", manual_candidate, merged_manual_text is not None),
            ("library", lib_candidate, merged_lib_text is not None),
        )
        if present
    }
    topology_errors = _proving_merged_topology_errors(
        proving_merged_directory,
        expected_candidates,
        require_present=False,
    )
    merged_manual = (
        fixed_path_under(
            manual_candidate,
            proving_merged_directory,
            label="proving_merged manual",
        )
        if merged_manual_text is not None and not topology_errors
        else None
    )
    proving_merged_lib = (
        fixed_path_under(
            lib_candidate,
            proving_merged_directory,
            label="proving_merged library",
        )
        if merged_lib_text is not None and not topology_errors
        else None
    )
    # Atomic replacement avoids following a hardlink/FIFO already occupying a
    # candidate leaf while preserving the mechanically merged source.  Formal
    # identity is checked by declaration/proof tokens; harmless formatting is
    # intentionally not restored from the seed.
    if (
        not topology_errors
        and merged_manual is not None
        and merged_manual_text is not None
    ):
        write_bytes(
            merged_manual,
            merged_manual_text.encode("utf-8"),
            label="proving_merged manual",
        )
    if (
        not topology_errors
        and proving_merged_lib is not None
        and merged_lib_text is not None
    ):
        write_bytes(
            proving_merged_lib,
            merged_lib_text.encode("utf-8"),
            label="proving_merged library",
        )
    if not topology_errors:
        topology_errors.extend(
            _proving_merged_topology_errors(
                proving_merged_directory,
                expected_candidates,
                require_present=True,
            )
        )
    errors.extend(topology_errors)
    forbidden: list[dict[str, Any]] = []
    if not topology_errors:
        for candidate_path in (merged_manual, proving_merged_lib):
            if candidate_path is not None:
                forbidden.extend(_forbidden_findings(candidate_path))
    if forbidden:
        errors.append("proving_merged candidate uses forbidden lemmas")

    ready = not errors and set(solved) == set(target_witnesses)
    parent_check: dict[str, Any] = {"status": "skipped"}
    if ready:
        if goal_check_file is None:
            raise SystemExit("goal_check_file is required for parent verification")
        else:
            declared_goal_check = goal_check_file.expanduser()
            if declared_goal_check.is_absolute():
                try:
                    goal_check_rel = declared_goal_check.resolve().relative_to(main_root)
                except ValueError as exc:
                    raise SystemExit(
                        "goal_check_file must be under the main root"
                    ) from exc
            else:
                goal_check_rel = declared_goal_check
        if (
            goal_check_rel.is_absolute()
            or ".." in goal_check_rel.parts
            or not goal_check_rel.parts
            or goal_check_rel.parts[0] != "Rocq"
        ):
            raise SystemExit("goal_check_file must be a formal repository-relative path")
        overlays: dict[Path, Path] = {}
        if merged_manual is not None:
            overlays[proof_manual_rel] = merged_manual
        if proving_merged_lib is not None:
            overlays[formal_case_lib_rel] = proving_merged_lib
        parent_check = run_coqc_check(
            workspace_root=main_root,
            build_workspace=run_builds_root(run_root) / round_id / "parent" / "src",
            target_file=goal_check_rel,
            target_kind="check",
            source_goal_version=str(base["source_goal_version"]),
            timeout_seconds=coq_timeout_seconds,
            overlays=overlays,
            current_case_anchor=(
                proof_manual_rel if merged_manual is not None else goal_check_rel
            ),
        )
        if parent_check.get("status") != "passed":
            ready = False
            errors.append("proving_merged candidate failed parent full check")

    parent_failure = (
        parent_check.get("first_failure")
        if isinstance(parent_check.get("first_failure"), dict)
        else None
    )
    first_failure = (
        parent_failure
        or (
            {
                "category": "merge",
                "kind": "proving-merged-failed",
                "message": str(errors[0]),
            }
            if errors
            else None
        )
    )
    reuse_summary = _merge_reuse_measurements(reuse_measurements)
    result: dict[str, Any] = {
        "status": "passed" if ready else "failed",
        "source_goal_version": base.get("source_goal_version"),
        "candidate": {
            "proof_manual_sha256": (
                _sha256(merged_manual)
                if merged_manual is not None and not topology_errors
                else None
            ),
            "proving_merged_lib_sha256": (
                _sha256(proving_merged_lib)
                if proving_merged_lib is not None and not topology_errors
                else None
            ),
        },
        "group_count": len(context["manifest"]["groups"]),
        "added_declarations": _compact_declarations(added_declarations),
    }
    if reuse_summary:
        result["proof_reuse"] = reuse_summary
    if not ready:
        result.update(
            {
                "error_count": len(errors),
                "blocker_count": 0,
                **({"failure": first_failure} if first_failure else {}),
            }
        )
    write_json(report_directory / "proving_merged_result.json", result)
    return result
