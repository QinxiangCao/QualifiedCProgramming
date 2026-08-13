#!/usr/bin/env python3
"""Prepare copied group files and compact group-worker handoffs."""

# ruff: noqa: E402 -- internal sibling modules are resolved from this script directory.

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from file_integrity import sha256_bytes
from file_integrity import sha256_file as _sha256
from group_plan_utils import group_entries_from_plan, load_group_plan
from path_utils import (
    fixed_path_under,
    group_worker_commands,
    init_group_worker_files,
    main_root_from_run_root,
    path_is_link_like,
    prepare_group_directory,
    reports_root,
    slug,
    write_bytes,
    write_json,
)
from proof_manual_utils import (
    ensure_unique_lemma_names,
    helper_namespace_for_group_id,
    markdown_table_cells,
    normalize_reuse_decision,
    parse_manual_file,
)
from public_helper_utils import (
    freeze_round_public_helper_snapshot,
)

GROUP_WORKERS_MANIFEST_NAME = "group_workers_manifest.json"
SHA256_RE = re.compile(r"[0-9a-f]{64}")


def _load_object(path: Path) -> dict[str, Any]:
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
        elif isinstance(value, str) and SHA256_RE.fullmatch(value):
            result[key] = value
        else:
            raise SystemExit(
                f"base manifest seed_sha256.{key} must be sha256 or null"
            )
    return result


def _validate_seed_artifact(path: Path, digest: str | None, *, label: str) -> None:
    if digest is None:
        if os.path.lexists(path):
            raise SystemExit(f"{label} appeared after base manifest creation")
        return
    if path_is_link_like(path) or not path.is_file() or _sha256(path) != digest:
        raise SystemExit(f"{label} changed after base manifest creation")


def _base_formal_artifact_paths(
    base: dict[str, Any], *, main_root: Path
) -> tuple[Path, Path]:
    """Resolve the two canonical base identities without following their leaves."""

    relatives: dict[str, Path] = {}
    for key in ("proof_manual", "formal_case_lib"):
        raw = base.get(key)
        relative = Path(str(raw or ""))
        if (
            not isinstance(raw, str)
            or not raw
            or relative.is_absolute()
            or ".." in relative.parts
            or relative.as_posix() != raw
            or not relative.parts
            or relative.parts[0] != "Rocq"
            or relative.suffix != ".v"
        ):
            raise SystemExit(
                f"base manifest {key} must be a canonical repository-relative Rocq file"
            )
        relatives[key] = relative
    manual_relative = relatives["proof_manual"]
    lib_relative = relatives["formal_case_lib"]
    manual_prefix = manual_relative.stem.removesuffix("_proof_manual")
    lib_prefix = lib_relative.stem.removesuffix("_lib")
    if (
        manual_relative.parent != lib_relative.parent
        or not manual_prefix
        or manual_prefix == manual_relative.stem
        or not lib_prefix
        or lib_prefix == lib_relative.stem
        or manual_prefix != lib_prefix
    ):
        raise SystemExit(
            "base manifest proof_manual/formal_case_lib identities do not match"
        )
    manual_parent = fixed_path_under(
        (main_root / manual_relative).parent,
        main_root,
        label="formal proof manual parent",
    )
    lib_parent = fixed_path_under(
        (main_root / lib_relative).parent,
        main_root,
        label="formal case library parent",
    )
    return manual_parent / manual_relative.name, lib_parent / lib_relative.name


def _reuse_available(path: Path) -> bool:
    """Return whether a canonical hint contains any reusable proof/helper unit."""

    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not (stripped.startswith("|") and stripped.endswith("|")):
            continue
        cells = markdown_table_cells(stripped)
        if len(cells) >= 2 and normalize_reuse_decision(cells[1]) in {
            "direct copy",
            "partial proof-idea reuse",
        }:
            return True
    return False


def dispatch_order_for_entries(entries: list[dict[str, Any]]) -> list[str]:
    """Deterministically prioritize no-reuse, difficult, structurally heavy groups."""

    priorities: list[tuple[bool, int, int, int, str]] = []
    for fallback_index, entry in enumerate(entries):
        hint = Path(str(entry.get("proof_reuse") or ""))
        has_reuse = (
            bool(entry.get("proof_reuse")) and hint.is_file() and _reuse_available(hint)
        )
        aggressive_split_count = sum(
            len(witness.get("split_goals", []))
            for witness in entry.get("witnesses", [])
            if isinstance(witness, dict)
            and witness.get("proof_mode") == "aggressive_pre_process"
        )
        structural_load = (
            len(entry.get("witnesses", []))
            + 2 * aggressive_split_count
            + 2 * len(entry.get("helpers", []))
        )
        priorities.append(
            (
                has_reuse,
                -int(entry.get("estimated_difficulty", 1)),
                -structural_load,
                int(entry.get("index", fallback_index)),
                str(entry["id"]),
            )
        )
    return [item[-1] for item in sorted(priorities)]


def resolve_group_workers_manifest(
    manifest_path: Path,
    *,
    main_root: Path | None = None,
    validate_current_seed: bool = True,
    seed_root: Path | None = None,
    expected_run_root: Path | None = None,
    expected_round: str | None = None,
) -> dict[str, Any]:
    """Expand the compact controller manifest from its fixed layout and seals."""

    manifest_path = manifest_path.expanduser().absolute()
    if main_root is None:
        if len(manifest_path.parents) < 5:
            raise SystemExit("group workers manifest path is too shallow")
        main_root = manifest_path.parents[4]
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
            "group workers manifest is outside the fixed report root"
        ) from exc
    if (
        len(report_relative.parts) != 4
        or report_relative.parts[1] != "rounds"
        or report_relative.parts[3] != GROUP_WORKERS_MANIFEST_NAME
    ):
        raise SystemExit("group workers manifest does not use the fixed report layout")
    run_id, _rounds, report_round, _name = report_relative.parts
    if expected_round is not None:
        if (
            not isinstance(expected_round, str)
            or not expected_round
            or Path(expected_round).name != expected_round
            or Path(expected_round).is_absolute()
            or report_round != slug(expected_round)
        ):
            raise SystemExit(
                "group workers manifest round differs from the expected current round"
            )
        round_id = expected_round
    else:
        round_id = report_round
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
        if (
            expected_run.parent != main_root / "verification_runs"
            or run_root != expected_run
        ):
            raise SystemExit(
                "group workers manifest is not bound to the expected current run"
            )
    seed_owner = main_root
    if seed_root is not None:
        expected_seed_root = fixed_path_under(
            run_root / round_id / "reuse_source_raw",
            run_root,
            label="sealed manifest seed root",
        )
        candidate_seed_root = seed_root.expanduser().absolute()
        if candidate_seed_root != expected_seed_root:
            raise SystemExit(
                "group workers manifest seed root differs from its fixed round topology"
            )
        seed_owner = fixed_path_under(
            candidate_seed_root,
            run_root,
            label="sealed manifest seed root",
        )
        if not seed_owner.is_dir():
            raise SystemExit("group workers manifest seed root is not a directory")
    raw = _load_object(manifest_path)
    if set(raw) != {
        "base_manifest_sha256",
        "group_plan",
        "group_plan_sha256",
        "public_helper_snapshot_sha256",
        "groups",
        "dispatch_order",
    }:
        raise SystemExit("group workers manifest contains unsupported fields")
    compact_groups = raw.get("groups")
    if (
        not isinstance(compact_groups, list)
        or not all(isinstance(item, dict) for item in compact_groups)
    ):
        raise SystemExit("group workers manifest groups must be an object list")
    compact_ids: list[str] = []
    for item in compact_groups:
        allowed = {
            "id",
            "proof_reuse_sha256",
            "proof_reuse_sources",
        }
        if set(item) - allowed or not isinstance(item.get("id"), str) or not item["id"]:
            raise SystemExit("group workers manifest group has invalid fields")
        if ("proof_reuse_sha256" in item) != ("proof_reuse_sources" in item):
            raise SystemExit(
                "group workers manifest proof reuse seal is incomplete"
            )
        compact_ids.append(str(item["id"]))
    if len(compact_ids) != len(set(compact_ids)):
        raise SystemExit("group workers manifest group ids must be unique")

    report_root = fixed_path_under(
        main_root / "reports" / run_id,
        main_root,
        label="report root",
    )
    vc_directory = fixed_path_under(
        run_root / round_id,
        run_root,
        label="vc-proving round directory",
    )
    base_path = fixed_path_under(
        vc_directory / "base_manifest.json",
        vc_directory,
        label="base manifest",
    )
    if (
        not base_path.is_file()
        or _sha256(base_path) != raw.get("base_manifest_sha256")
    ):
        raise SystemExit("group workers manifest base seal changed")
    base = _load_object(base_path)
    if set(base) != {
        "source_goal_version",
        "proof_manual",
        "formal_case_lib",
        "seed_sha256",
    }:
        raise SystemExit("group workers manifest base is invalid")

    plan_relative = Path(str(raw.get("group_plan") or ""))
    if plan_relative.is_absolute() or ".." in plan_relative.parts:
        raise SystemExit("group workers manifest group plan path is invalid")
    plan_path = fixed_path_under(
        report_root / plan_relative,
        report_root,
        label="sealed group plan",
    )
    plan_sha256 = str(raw.get("group_plan_sha256") or "")
    if (
        not plan_path.is_file()
        or not plan_sha256
        or _sha256(plan_path) != plan_sha256
    ):
        raise SystemExit("group workers manifest group plan seal changed")

    formal_manual, formal_case_lib = _base_formal_artifact_paths(
        base,
        main_root=seed_owner,
    )
    seed = _seed_digests(base)
    has_manual = seed["proof_manual"] is not None
    has_formal_case_lib = seed["formal_case_lib"] is not None
    if validate_current_seed:
        _validate_seed_artifact(
            formal_manual, seed["proof_manual"], label="formal proof manual"
        )
        _validate_seed_artifact(
            formal_case_lib, seed["formal_case_lib"], label="formal_case_lib"
        )
    plan = load_group_plan(plan_path)
    if has_manual:
        if not formal_manual.is_file():
            raise SystemExit("group workers manifest formal proof manual is missing")
        _prelude, lemmas = parse_manual_file(
            formal_manual.read_text(encoding="utf-8")
        )
        ensure_unique_lemma_names(lemmas)
    else:
        if plan.get("groups"):
            raise SystemExit("accepted group plan requires a proof manual")
        lemmas = []
    planned = group_entries_from_plan(
        lemmas,
        plan,
        require_accepted=True,
    )
    if not has_formal_case_lib and any(
        group.get("planned_helpers") for group in planned
    ):
        raise SystemExit(
            "accepted group plan cannot declare helpers without formal_case_lib"
        )
    if [str(item["group_id"]) for item in planned] != compact_ids:
        raise SystemExit("group workers manifest groups do not match the accepted plan")

    public_helper_path = fixed_path_under(
        vc_directory / "public_helper_snapshot.txt",
        vc_directory,
        label="public helper snapshot",
    )
    public_sha256 = str(raw.get("public_helper_snapshot_sha256") or "")
    if (
        not public_helper_path.is_file()
        or not public_sha256
        or _sha256(public_helper_path) != public_sha256
    ):
        raise SystemExit("group workers manifest public helper snapshot changed")

    entries: list[dict[str, Any]] = []
    for index, (group, compact) in enumerate(
        zip(planned, compact_groups, strict=True)
    ):
        group_id = str(group["group_id"])
        directory_name = f"group_{index:02d}__{slug(group_id)}"
        directory = fixed_path_under(
            vc_directory / "groups" / directory_name,
            vc_directory,
            label="group directory",
        )
        report_directory = fixed_path_under(
            report_root / "rounds" / report_round / "groups" / directory_name,
            report_root,
            label="group report directory",
        )
        entry: dict[str, Any] = {
            "id": group_id,
            "index": index,
            "estimated_difficulty": int(group["estimated_difficulty"]),
            "directory": str(directory),
            "proof_manual": str(directory / formal_manual.name),
            "report_directory": str(report_directory),
            "witnesses": [
                {
                    "name": str(witness["name"]),
                    "proof_mode": str(witness["proof_mode"]),
                    **(
                        {"strategy": str(witness["strategy"])}
                        if "strategy" in witness
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
                for witness in group["witnesses"]
            ],
            "helper_namespace": helper_namespace_for_group_id(group_id),
            "helpers": [
                dict(item) for item in group.get("planned_helpers", [])
            ],
            "public_helper_lemma_lib": str(public_helper_path),
            "public_helper_lemma_lib_sha256": public_sha256,
        }
        if has_formal_case_lib:
            entry["group_worker_lib"] = str(directory / formal_case_lib.name)
        if "proof_reuse_sha256" in compact:
            hint_path = fixed_path_under(
                report_directory / "proof_reuse.md",
                report_directory,
                label="proof reuse handoff",
            )
            hint_sha256 = str(compact["proof_reuse_sha256"])
            if (
                not hint_path.is_file()
                or not hint_sha256
                or _sha256(hint_path) != hint_sha256
            ):
                raise SystemExit(
                    f"group workers manifest proof reuse hint changed: {group_id}"
                )
            sources = compact.get("proof_reuse_sources")
            if not isinstance(sources, list):
                raise SystemExit(
                    f"group workers manifest proof reuse sources are invalid: {group_id}"
                )
            source_records: list[dict[str, str]] = []
            for source in sources:
                if (
                    not isinstance(source, dict)
                    or set(source) != {"relative_path", "sha256"}
                ):
                    raise SystemExit(
                        f"group workers manifest proof reuse source is invalid: {group_id}"
                    )
                relative = Path(str(source.get("relative_path") or ""))
                if relative.is_absolute() or ".." in relative.parts:
                    raise SystemExit(
                        f"group workers manifest proof reuse source path is invalid: {group_id}"
                    )
                source_path = fixed_path_under(
                    main_root / relative,
                    main_root,
                    label="proof reuse source",
                )
                source_sha256 = str(source.get("sha256") or "")
                if (
                    not source_path.is_file()
                    or not source_sha256
                    or _sha256(source_path) != source_sha256
                ):
                    raise SystemExit(
                        f"group workers manifest proof reuse source changed: {group_id}"
                    )
                source_records.append(
                    {"path": str(source_path), "sha256": source_sha256}
                )
            entry.update(
                {
                    "proof_reuse": str(hint_path),
                    "proof_reuse_sha256": hint_sha256,
                    "proof_reuse_sources": source_records,
                }
            )
        entries.append(entry)
    dispatch_order = raw.get("dispatch_order")
    if (
        not isinstance(dispatch_order, list)
        or [str(item) for item in dispatch_order] != dispatch_order
        or dispatch_order != dispatch_order_for_entries(entries)
    ):
        raise SystemExit("group workers manifest dispatch order is invalid")
    return {
        "round": round_id,
        "source_goal_version": base["source_goal_version"],
        "base_manifest": str(base_path),
        "proof_manual": base["proof_manual"],
        "formal_case_lib": base["formal_case_lib"],
        "public_helper_lemma_lib": str(public_helper_path),
        "public_helper_lemma_lib_sha256": public_sha256,
        "groups": entries,
        "order": compact_ids,
        "dispatch_order": dispatch_order,
    }


def prepare_group_workers(
    base_manifest_path: Path,
    *,
    group_plan_path: Path,
    force_groups: bool = False,
    max_compact_attempts: int = 3,
    reuse_hints: dict[str, dict[str, Any]] | None = None,
    expected_proof_manual: str | None = None,
    expected_formal_case_lib: str | None = None,
    expected_run_root: Path | None = None,
    expected_round: str | None = None,
) -> list[dict[str, Any]]:
    del (
        max_compact_attempts
    )  # retry policy belongs to controller state, not the manifest.
    # Derive ownership from the lexical canonical layout before loading any
    # controller artifact.  Resolving first would hide a replaced manifest or
    # round-directory symlink.
    base_manifest_path = base_manifest_path.expanduser().absolute()
    vc_directory = base_manifest_path.parent
    run_root = vc_directory.parent
    main_root = main_root_from_run_root(run_root)
    base_manifest_path = fixed_path_under(
        base_manifest_path,
        run_root,
        label="vc-proving base manifest",
    )
    if base_manifest_path != vc_directory / "base_manifest.json":
        raise SystemExit(
            "vc-proving base manifest does not use its exact round path"
        )
    if expected_run_root is not None:
        expected_run = fixed_path_under(
            expected_run_root,
            main_root,
            label="expected current run root",
        )
        if expected_run != run_root:
            raise SystemExit(
                "vc-proving base manifest is not bound to the expected current run"
            )
    base = _load_object(base_manifest_path)
    if set(base) != {
        "source_goal_version",
        "proof_manual",
        "formal_case_lib",
        "seed_sha256",
    }:
        raise SystemExit("base manifest contains unsupported or missing fields")
    if (expected_proof_manual is None) != (expected_formal_case_lib is None):
        raise SystemExit("expected base formal identities must be supplied together")
    if expected_proof_manual is not None and (
        base.get("proof_manual") != expected_proof_manual
        or base.get("formal_case_lib") != expected_formal_case_lib
    ):
        raise SystemExit(
            "base manifest formal identities do not match controller target files"
        )

    round_id = vc_directory.name
    if expected_round is not None and round_id != expected_round:
        raise SystemExit(
            "vc-proving base manifest is not bound to the expected current round"
        )
    report_owner = reports_root(run_root)
    report_directory = fixed_path_under(
        report_owner / "rounds" / slug(round_id),
        report_owner,
        label="vc-proving report directory",
    )
    group_plan_path = fixed_path_under(
        group_plan_path,
        report_owner,
        label="accepted group plan",
    )
    if not group_plan_path.is_file():
        raise SystemExit(f"accepted group plan is missing: {group_plan_path}")

    formal_manual, formal_case_lib = _base_formal_artifact_paths(
        base,
        main_root=main_root,
    )
    seed = _seed_digests(base)
    has_manual = seed["proof_manual"] is not None
    has_formal_case_lib = seed["formal_case_lib"] is not None
    _validate_seed_artifact(
        formal_manual, seed["proof_manual"], label="formal proof manual"
    )
    _validate_seed_artifact(
        formal_case_lib, seed["formal_case_lib"], label="formal_case_lib"
    )
    plan = load_group_plan(group_plan_path)
    if has_manual:
        _prelude, lemmas = parse_manual_file(
            formal_manual.read_text(encoding="utf-8")
        )
        ensure_unique_lemma_names(lemmas)
    else:
        if plan.get("groups"):
            raise SystemExit("accepted group plan requires a proof manual")
        lemmas = []
    groups = group_entries_from_plan(
        lemmas,
        plan,
        require_accepted=True,
    )
    if not has_formal_case_lib and any(
        group.get("planned_helpers") for group in groups
    ):
        raise SystemExit(
            "accepted group plan cannot declare helpers without formal_case_lib"
        )
    groups_directory = vc_directory / "groups"
    manifest_path = report_directory / GROUP_WORKERS_MANIFEST_NAME
    entries: list[dict[str, Any]] = []
    public_helper_snapshot = freeze_round_public_helper_snapshot(run_root, round_id)
    public_helper_path = Path(str(public_helper_snapshot["path"]))
    public_helper_sha256 = str(public_helper_snapshot["sha256"])

    for index, group in enumerate(groups):
        group_id = str(group["group_id"])
        namespace = helper_namespace_for_group_id(group_id)
        directory, group_manual, group_worker_lib = prepare_group_directory(
            groups_root=groups_directory,
            group_id=group_id,
            index=index,
            formal_manual=formal_manual,
            formal_case_lib=(formal_case_lib if has_formal_case_lib else None),
            run_root=run_root,
            force=force_groups,
        )
        report_dir = fixed_path_under(
            report_directory / "groups" / directory.name,
            report_owner,
            label="fixed group report directory",
        )
        commands = group_worker_commands(
            main_root=main_root,
            run_root=run_root,
            round_id=round_id,
            group_id=group_id,
            group_directory=directory,
        )
        entry = {
            "id": group_id,
            "index": index,
            "estimated_difficulty": int(group["estimated_difficulty"]),
            "directory": str(directory),
            "proof_manual": str(group_manual),
            "report_directory": str(report_dir),
            "witnesses": [
                {
                    "name": str(witness["name"]),
                    "proof_mode": str(witness["proof_mode"]),
                    **(
                        {"strategy": str(witness["strategy"])}
                        if "strategy" in witness
                        else {}
                    ),
                    "split_goals": [
                        {
                            "name": str(split_goal["name"]),
                            **(
                                {"strategy": str(split_goal["strategy"])}
                                if str(split_goal.get("strategy") or "")
                                else {}
                            ),
                        }
                        for split_goal in witness["split_goals"]
                    ],
                }
                for witness in group["witnesses"]
            ],
            "helper_namespace": namespace,
            "helpers": [dict(item) for item in group.get("planned_helpers", [])],
            "public_helper_lemma_lib": str(public_helper_path),
            "public_helper_lemma_lib_sha256": public_helper_sha256,
        }
        if group_worker_lib is not None:
            entry["group_worker_lib"] = str(group_worker_lib)
        if reuse_hints:
            hint = reuse_hints.get(group_id)
            if not isinstance(hint, dict):
                raise SystemExit(
                    f"accepted reuse hint is missing for group: {group_id}"
                )
            source_hint = fixed_path_under(
                Path(str(hint.get("path") or "")),
                main_root,
                label="accepted proof reuse hint",
            )
            expected_hint_sha256 = str(hint.get("sha256") or "")
            try:
                source_hint_bytes = source_hint.read_bytes()
            except OSError as exc:
                raise SystemExit(
                    f"accepted reuse hint cannot be read before preparing group: {group_id}: {exc}"
                ) from exc
            if sha256_bytes(source_hint_bytes) != expected_hint_sha256:
                raise SystemExit(
                    f"accepted reuse hint changed before preparing group: {group_id}"
                )
            proof_reuse = report_dir / "proof_reuse.md"
            write_bytes(
                proof_reuse,
                source_hint_bytes,
                label="group proof reuse handoff",
            )
            entry["proof_reuse"] = str(proof_reuse)
            entry["proof_reuse_sha256"] = expected_hint_sha256
            raw_sources = hint.get("sources")
            if not isinstance(raw_sources, list) or not all(
                isinstance(item, dict) for item in raw_sources
            ):
                raise SystemExit(
                    f"accepted reuse hint source records are invalid: {group_id}"
                )
            source_records: list[dict[str, str]] = []
            for item in raw_sources:
                source = fixed_path_under(
                    Path(str(item.get("path") or "")),
                    main_root,
                    label="accepted proof reuse source",
                )
                source_sha256 = str(item.get("sha256") or "")
                if (
                    not source.is_file()
                    or not source_sha256
                    or _sha256(source) != source_sha256
                ):
                    raise SystemExit(
                        f"accepted proof reuse source changed before preparing group: {group_id}"
                    )
                source_records.append({"path": str(source), "sha256": source_sha256})
            if source_records:
                entry["proof_reuse_sources"] = source_records
        init_group_worker_files(
            report_dir=report_dir,
            group=entry,
            formal_case_lib=(base["formal_case_lib"] if has_formal_case_lib else None),
            commands=commands,
        )
        entries.append(entry)

    compact_groups: list[dict[str, Any]] = []
    for entry in entries:
        compact: dict[str, Any] = {"id": str(entry["id"])}
        if entry.get("proof_reuse"):
            compact["proof_reuse_sha256"] = str(entry["proof_reuse_sha256"])
            compact["proof_reuse_sources"] = [
                {
                    "relative_path": Path(str(source["path"]))
                    .relative_to(main_root)
                    .as_posix(),
                    "sha256": str(source["sha256"]),
                }
                for source in entry.get("proof_reuse_sources", [])
            ]
        compact_groups.append(compact)
    manifest = {
        "base_manifest_sha256": _sha256(base_manifest_path),
        "group_plan": group_plan_path.relative_to(report_owner).as_posix(),
        "group_plan_sha256": _sha256(group_plan_path),
        "public_helper_snapshot_sha256": public_helper_sha256,
        "groups": compact_groups,
        "dispatch_order": dispatch_order_for_entries(entries),
    }
    write_json(manifest_path, manifest)
    return entries


def load_group_workers_manifest(
    manifest_or_report_directory: Path,
) -> list[dict[str, Any]]:
    path = manifest_or_report_directory
    if path.is_dir():
        path = path / GROUP_WORKERS_MANIFEST_NAME
    payload = resolve_group_workers_manifest(path)
    groups = payload.get("groups")
    if not isinstance(groups, list):
        raise SystemExit(f"invalid group workers manifest: {path}")
    return groups
