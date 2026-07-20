#!/usr/bin/env python3
"""Create the immutable base manifest for a vc-proving preparation step."""

# ruff: noqa: E402 -- internal sibling modules are resolved from this script directory.

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from path_utils import (
    main_root_from_run_root,
    relative_to_root,
    reports_root,
    write_json,
)
from proof_manual_utils import (
    ensure_unique_lemma_names,
    lemma_statement_hash,
    parse_manual_file,
)


BASE_MANIFEST_NAME = "base_manifest.json"
VC_PROVING_ROUND_RE = re.compile(r"^.+-vc-proving-r\d+$")


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
    run_root = run_root.expanduser().resolve()
    manual_file = manual_file.expanduser().resolve()
    formal_case_lib = formal_case_lib.expanduser().resolve()
    round_report_directory = round_report_directory.expanduser().resolve()
    if main_root_from_run_root(run_root) != main_root:
        raise SystemExit("run root is not owned by --main-root")
    if not VC_PROVING_ROUND_RE.fullmatch(vc_proving_round_id):
        raise SystemExit(f"vc-proving round id must look like <case>-vc-proving-rN: {vc_proving_round_id}")
    expected_report = reports_root(run_root) / "rounds" / vc_proving_round_id
    if round_report_directory != expected_report:
        raise SystemExit(f"round report directory must be {expected_report}: {round_report_directory}")
    if not manual_file.is_file():
        raise SystemExit(f"proof manual not found: {manual_file}")
    if not formal_case_lib.is_file():
        raise SystemExit(f"formal_case_lib not found: {formal_case_lib}")
    manual_rel = relative_to_root(manual_file, main_root)
    formal_case_lib_rel = relative_to_root(formal_case_lib, main_root)
    if manual_rel is None or formal_case_lib_rel is None:
        raise SystemExit("proof manual and formal_case_lib must be under the main root")
    if manual_rel.parts[:1] != ("SeparationLogic",) or formal_case_lib_rel.parts[:1] != ("SeparationLogic",):
        raise SystemExit("proof manual and formal_case_lib must be formal files under SeparationLogic")

    text = manual_file.read_text(encoding="utf-8")
    _prelude, lemmas = parse_manual_file(text)
    ensure_unique_lemma_names(lemmas)
    lemma_names = [str(lemma["name"]) for lemma in lemmas]
    if goals:
        missing = [name for name in goals if name not in set(lemma_names)]
        if missing:
            raise SystemExit("unknown witness lemma(s): " + ", ".join(missing))
        target_names = list(dict.fromkeys(goals))
    else:
        target_names = lemma_names
    container = (run_root / vc_proving_round_id).resolve()
    groups_directory = container / "groups"
    proving_merged_directory = container / "proving_merged"
    groups_directory.mkdir(parents=True, exist_ok=True)
    proving_merged_directory.mkdir(parents=True, exist_ok=True)
    round_report_directory.mkdir(parents=True, exist_ok=True)
    base_manifest_path = container / BASE_MANIFEST_NAME
    manifest = {
        "schema_version": "qcp-vc-proving-base-manifest/v2",
        "round": vc_proving_round_id,
        "source_goal_version": source_goal_version,
        "proof_manual": manual_rel.as_posix(),
        "formal_case_lib": formal_case_lib_rel.as_posix(),
        "seed_sha256": {
            "proof_manual": hashlib.sha256(manual_file.read_bytes()).hexdigest(),
            "formal_case_lib": hashlib.sha256(formal_case_lib.read_bytes()).hexdigest(),
        },
        "witnesses": [
            {
                "name": str(lemma["name"]),
                "statement_hash": lemma_statement_hash(lemma),
            }
            for lemma in lemmas
            if str(lemma["name"]) in set(target_names)
        ],
    }
    write_json(base_manifest_path, manifest)
    return base_manifest_path
