#!/usr/bin/env python3
"""Prepare copied group files and compact group-worker handoffs."""

# ruff: noqa: E402 -- internal sibling modules are resolved from this script directory.

from __future__ import annotations

import hashlib
import json
import shlex
import sys
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from group_plan_utils import group_entries_from_plan, load_group_plan
from path_utils import (
    init_group_worker_files,
    main_root_from_run_root,
    prepare_group_directory,
    reports_root,
    write_json,
)
from proof_manual_utils import (
    ensure_unique_lemma_names,
    helper_namespace_for_group_id,
    lemma_statement_hash,
    parse_manual_file,
)


GROUP_WORKERS_MANIFEST_NAME = "group_workers_manifest.json"


def _load_object(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise SystemExit(f"JSON file must contain an object: {path}")
    return payload


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _dependency_ready_order(groups: list[dict[str, Any]]) -> list[str]:
    remaining = {str(group["id"]): group for group in groups}
    ready_done: set[str] = set()
    order: list[str] = []
    while remaining:
        ready = [group for group in remaining.values() if all(dep in ready_done for dep in group.get("depends_on", []))]
        if not ready:
            raise SystemExit("group plan contains a dependency cycle")
        for group in ready:
            group_id = str(group["id"])
            order.append(group_id)
            ready_done.add(group_id)
            remaining.pop(group_id)
    return order


def prepare_group_workers(
    base_manifest_path: Path,
    *,
    group_plan_path: Path,
    force_groups: bool = False,
    max_compact_attempts: int = 3,
) -> list[dict[str, Any]]:
    del max_compact_attempts  # retry policy belongs to controller state, not the manifest.
    base_manifest_path = base_manifest_path.expanduser().resolve()
    base = _load_object(base_manifest_path)
    if base.get("schema_version") != "qcp-vc-proving-base-manifest/v2":
        raise SystemExit("base manifest schema_version must be qcp-vc-proving-base-manifest/v2")

    vc_directory = base_manifest_path.parent
    run_root = vc_directory.parent
    main_root = main_root_from_run_root(run_root)
    round_id = str(base.get("round") or "")
    if vc_directory.name != round_id:
        raise SystemExit("base manifest round does not match its fixed directory")
    report_directory = reports_root(run_root) / "rounds" / round_id
    group_plan_path = group_plan_path.expanduser().resolve()
    if not group_plan_path.is_file():
        raise SystemExit(f"accepted group plan is missing: {group_plan_path}")

    formal_manual = main_root / str(base["proof_manual"])
    formal_case_lib = main_root / str(base["formal_case_lib"])
    if not formal_manual.is_file() or not formal_case_lib.is_file():
        raise SystemExit("formal manual and formal_case_lib must exist before group preparation")
    seed = base.get("seed_sha256") if isinstance(base.get("seed_sha256"), dict) else {}
    if seed.get("proof_manual") != _sha256(formal_manual) or seed.get("formal_case_lib") != _sha256(formal_case_lib):
        raise SystemExit("formal manual or formal_case_lib changed after base manifest creation")

    _prelude, lemmas = parse_manual_file(formal_manual.read_text(encoding="utf-8"))
    ensure_unique_lemma_names(lemmas)
    expected_witnesses = base.get("witnesses") if isinstance(base.get("witnesses"), list) else []
    expected_hashes = {str(item["name"]): str(item["statement_hash"]) for item in expected_witnesses}
    current = [lemma for lemma in lemmas if str(lemma["name"]) in expected_hashes]
    if {str(item["name"]): lemma_statement_hash(item) for item in current} != expected_hashes:
        raise SystemExit("base manifest witness statements are stale")

    groups = group_entries_from_plan(
        current,
        load_group_plan(group_plan_path),
        require_controller_verified=True,
        source_goal_version=str(base["source_goal_version"]),
    )
    groups_directory = vc_directory / "groups"
    controller = main_root / ".agents" / "skills" / "verification-orchestrator" / "scripts" / "controller.py"
    manifest_path = report_directory / GROUP_WORKERS_MANIFEST_NAME
    entries: list[dict[str, Any]] = []

    for index, group in enumerate(groups):
        group_id = str(group["group_id"])
        namespace = helper_namespace_for_group_id(group_id)
        directory, group_manual, group_worker_lib = prepare_group_directory(
            groups_root=groups_directory,
            group_id=group_id,
            index=index,
            formal_manual=formal_manual,
            formal_case_lib=formal_case_lib,
            force=force_groups,
        )
        report_dir = report_directory / "groups" / directory.name
        check_argv = [
            "python3",
            str(controller),
            "--main-root",
            str(main_root),
            "coq-check",
            "--run",
            run_root.name,
            "--round",
            round_id,
            "--target-kind",
            "group-check",
            "--group",
            group_id,
        ]
        debug_argv = [
            "python3",
            str(controller),
            "--main-root",
            str(main_root),
            "coq-debug",
            "--run",
            run_root.name,
            "--round",
            round_id,
            "--group",
            group_id,
        ]
        entry = {
            "id": group_id,
            "index": index,
            "directory": str(directory),
            "proof_manual": str(group_manual),
            "group_worker_lib": str(group_worker_lib),
            "report_directory": str(report_dir),
            "witnesses": [str(name) for name in group["witness_names"]],
            "depends_on": [str(dep) for dep in group.get("dependencies", [])],
            "helper_namespace": namespace,
            "strategy": str(group.get("proof_strategy") or ""),
            "helpers": [str(item) for item in group.get("expected_helpers", [])],
            "check_command": shlex.join(check_argv),
            "debug_command": shlex.join(debug_argv),
            "debug_script": str(run_root / "_coq_builds" / round_id / directory.name / "src" / ".coq_debug" / f"{directory.name}.v"),
        }
        init_group_worker_files(
            report_dir=report_dir,
            group=entry,
            source_goal_version=str(base["source_goal_version"]),
            formal_case_lib=base["formal_case_lib"],
        )
        entries.append(entry)

    manifest = {
        "schema_version": "qcp-vc-proving-group-workers-manifest/v3",
        "round": round_id,
        "source_goal_version": base["source_goal_version"],
        "base_manifest": str(base_manifest_path),
        "proof_manual": base["proof_manual"],
        "formal_case_lib": base["formal_case_lib"],
        "groups": entries,
        "order": _dependency_ready_order(entries),
    }
    write_json(manifest_path, manifest)
    return entries


def load_group_workers_manifest(manifest_or_report_directory: Path) -> list[dict[str, Any]]:
    path = manifest_or_report_directory
    if path.is_dir():
        path = path / GROUP_WORKERS_MANIFEST_NAME
    payload = _load_object(path)
    groups = payload.get("groups")
    if not isinstance(groups, list):
        raise SystemExit(f"invalid group workers manifest: {path}")
    return groups
