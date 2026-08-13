#!/usr/bin/env python3
"""Create the immutable base manifest for a vc-proving preparation step."""

# ruff: noqa: E402 -- internal sibling modules are resolved from this script directory.

from __future__ import annotations

import os
import re
import stat
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from file_integrity import sha256_bytes
from path_utils import (
    fixed_path_under,
    main_root_from_run_root,
    path_is_link_like,
    reports_root,
    slug,
    write_json,
)
from proof_manual_utils import (
    ensure_unique_lemma_names,
    parse_manual_file,
    partition_manual_lemmas,
)

BASE_MANIFEST_NAME = "base_manifest.json"
VC_PROVING_ROUND_RE = re.compile(r"^.+-vc-proving-r\d+$")


def _optional_seed_snapshot(path: Path, *, label: str) -> bytes | None:
    """Read one fixed regular seed once, or confirm that it is truly absent."""

    try:
        linked_before = path.lstat()
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise SystemExit(f"cannot inspect {label}: {path}: {exc}") from exc
    if path_is_link_like(path) or not stat.S_ISREG(linked_before.st_mode):
        raise SystemExit(f"{label} must be a fixed regular file: {path}")

    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
        with os.fdopen(descriptor, "rb") as stream:
            opened_before = os.fstat(stream.fileno())
            if (
                not stat.S_ISREG(opened_before.st_mode)
                or (opened_before.st_dev, opened_before.st_ino)
                != (linked_before.st_dev, linked_before.st_ino)
            ):
                raise SystemExit(f"{label} changed while it was being sealed: {path}")
            payload = stream.read()
            opened_after = os.fstat(stream.fileno())
        linked_after = path.lstat()
    except OSError as exc:
        raise SystemExit(f"cannot read fixed {label}: {path}: {exc}") from exc

    before = (
        opened_before.st_dev,
        opened_before.st_ino,
        opened_before.st_mode,
        opened_before.st_size,
        opened_before.st_mtime_ns,
    )
    after = (
        opened_after.st_dev,
        opened_after.st_ino,
        opened_after.st_mode,
        opened_after.st_size,
        opened_after.st_mtime_ns,
    )
    if (
        before != after
        or path_is_link_like(path)
        or not stat.S_ISREG(linked_after.st_mode)
        or (linked_after.st_dev, linked_after.st_ino)
        != (opened_after.st_dev, opened_after.st_ino)
    ):
        raise SystemExit(f"{label} changed while it was being sealed: {path}")
    return payload


def create_base_manifest(
    *,
    manual_file: Path,
    formal_case_lib: Path,
    main_root: Path,
    run_root: Path,
    round_report_directory: Path,
    vc_proving_round_id: str,
    source_goal_version: str,
    goals: list[str] | None = None,
) -> Path:
    main_root = main_root.expanduser().resolve()
    run_root = fixed_path_under(run_root, main_root, label="run root")
    manual_file = fixed_path_under(
        manual_file, main_root, label="proof manual target"
    )
    formal_case_lib = fixed_path_under(
        formal_case_lib, main_root, label="formal_case_lib target"
    )
    round_report_directory = fixed_path_under(
        round_report_directory, main_root, label="round report directory"
    )
    if main_root_from_run_root(run_root) != main_root:
        raise SystemExit("run root is not owned by --main-root")
    if not VC_PROVING_ROUND_RE.fullmatch(vc_proving_round_id):
        raise SystemExit(
            f"vc-proving round id must look like <case>-vc-proving-rN: {vc_proving_round_id}"
        )
    expected_report = (
        reports_root(run_root) / "rounds" / slug(vc_proving_round_id)
    )
    if round_report_directory != expected_report:
        raise SystemExit(
            f"round report directory must be {expected_report}: {round_report_directory}"
        )
    manual_rel = manual_file.relative_to(main_root)
    formal_case_lib_rel = formal_case_lib.relative_to(main_root)
    if (
        not manual_rel.parts
        or manual_rel.parts[0] != "Rocq"
        or not formal_case_lib_rel.parts
        or formal_case_lib_rel.parts[0] != "Rocq"
    ):
        raise SystemExit(
            "proof manual and formal_case_lib must be formal files under Rocq"
        )

    manual_snapshot = _optional_seed_snapshot(
        manual_file, label="proof manual target"
    )
    formal_case_lib_snapshot = _optional_seed_snapshot(
        formal_case_lib, label="formal_case_lib target"
    )
    if manual_snapshot is not None:
        try:
            text = manual_snapshot.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise SystemExit(f"proof manual target is not UTF-8: {manual_file}") from exc
        _prelude, lemmas = parse_manual_file(text)
        ensure_unique_lemma_names(lemmas)
        witness_lemmas, _split_goal_lemmas = partition_manual_lemmas(lemmas)
        lemma_names = [str(lemma["name"]) for lemma in witness_lemmas]
        if goals:
            missing = [name for name in goals if name not in set(lemma_names)]
            if missing:
                raise SystemExit("unknown witness lemma(s): " + ", ".join(missing))
            if list(dict.fromkeys(goals)) != lemma_names:
                raise SystemExit(
                    "vc-proving uses the complete current witness set; partial selection is unsupported"
                )
    elif goals:
        raise SystemExit("vc-proving goals require a proof manual")
    container = fixed_path_under(
        run_root / vc_proving_round_id,
        run_root,
        label="vc-proving round directory",
    )
    groups_directory = container / "groups"
    proving_merged_directory = container / "proving_merged"
    groups_directory.mkdir(parents=True, exist_ok=True)
    proving_merged_directory.mkdir(parents=True, exist_ok=True)
    round_report_directory.mkdir(parents=True, exist_ok=True)
    base_manifest_path = container / BASE_MANIFEST_NAME
    manifest = {
        "source_goal_version": source_goal_version,
        "proof_manual": manual_rel.as_posix(),
        "formal_case_lib": formal_case_lib_rel.as_posix(),
        "seed_sha256": {
            "proof_manual": (
                sha256_bytes(manual_snapshot)
                if manual_snapshot is not None
                else None
            ),
            "formal_case_lib": (
                sha256_bytes(formal_case_lib_snapshot)
                if formal_case_lib_snapshot is not None
                else None
            ),
        },
    }
    write_json(base_manifest_path, manifest)
    return base_manifest_path
