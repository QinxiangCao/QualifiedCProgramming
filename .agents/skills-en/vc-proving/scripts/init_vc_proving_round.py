#!/usr/bin/env python3
"""Create a vc-proving group_workers_manifest.json under the round report directory."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from proof_manual_utils import (
    diagnostics_file_for_manual,
    diagnostics_snapshot_for_manual,
    ensure_unique_lemma_names,
    lemma_statement_hash,
    lemma_target_symbol,
    parse_manual_file,
)
from coq_tooling import fixed_flags, fixed_flags_hash, infer_case_config, infer_main_workspace_root
from worktree_utils import (
    REPORTS_DIR_NAME,
    git_toplevel,
    run_builds_root,
    run_root_from_path,
    relative_to_worktree,
    reports_root,
    write_json,
)

GROUP_WORKERS_MANIFEST_NAME = "group_workers_manifest.json"


def _infer_main_workspace_root_for_round(round_worktree: Path) -> Path:
    resolved = round_worktree.expanduser().resolve()
    if "worktrees" in resolved.parts:
        index = resolved.parts.index("worktrees")
        candidate = Path(*resolved.parts[:index])
        if (candidate / "dune-project").is_file() or (candidate / "SeparationLogic").is_dir():
            return candidate.resolve()
    return infer_main_workspace_root(round_worktree)


def main() -> int:
    parser = argparse.ArgumentParser(description="Create a vc-proving group-workers manifest.")
    parser.add_argument("manual_file", help="Path to the round worktree *_proof_manual.v file")
    parser.add_argument("--case-lib", required=True, help="Path to the current case_lib in the same round worktree")
    parser.add_argument(
        "--source-goal-version",
        required=True,
        help="Controller-produced source_goal_version digest from accepted annotation round",
    )
    parser.add_argument("--goals", nargs="*", default=None, help="Optional witness lemma names to prove")
    parser.add_argument(
        "--round-work-dir",
        default=None,
        help=(
            f"Optional vc-proving-preparing report directory under "
            f"{REPORTS_DIR_NAME}/<case>-YYYYMMDDHHMMSS/rounds/<case>-vc-proving-rN/"
        ),
    )
    parser.add_argument(
        "--vc-proving-round-id",
        default=None,
        help="Controller preparing container id, for example <case>-vc-proving-r1.",
    )
    args = parser.parse_args()

    manual_path = Path(args.manual_file).expanduser().resolve()
    case_lib = Path(args.case_lib).expanduser().resolve()
    if not manual_path.is_file():
        raise SystemExit(f"proof manual not found: {manual_path}")
    if not case_lib.is_file():
        raise SystemExit(f"case_lib not found: {case_lib}")
    round_worktree = git_toplevel(manual_path)
    if git_toplevel(case_lib) != round_worktree:
        raise SystemExit("proof manual and case_lib must be in the same round worktree")
    main_workspace_root = _infer_main_workspace_root_for_round(round_worktree)

    text = manual_path.read_text(encoding="utf-8")
    _prelude, lemmas = parse_manual_file(text)
    ensure_unique_lemma_names(lemmas)
    lemma_names = [str(lemma["name"]) for lemma in lemmas]
    if args.goals:
        missing = [name for name in args.goals if name not in set(lemma_names)]
        if missing:
            raise SystemExit("unknown witness lemma(s): " + ", ".join(missing))
        target_names = list(dict.fromkeys(args.goals))
    else:
        target_names = lemma_names
    target_set = set(target_names)

    if args.round_work_dir:
        work_dir = Path(args.round_work_dir).expanduser().resolve()
        provided_run_root = run_root_from_path(work_dir, main_workspace_root)
        if provided_run_root is None:
            raise SystemExit(
                f"--round-work-dir must be under {main_workspace_root / REPORTS_DIR_NAME}/<case>-YYYYMMDDHHMMSS/: {work_dir}"
            )
        expected_round_name = args.vc_proving_round_id or round_worktree.name
        expected_round_reports = reports_root(provided_run_root) / "rounds" / expected_round_name
        if work_dir != expected_round_reports:
            raise SystemExit(f"--round-work-dir must be the round report directory {expected_round_reports}: {work_dir}")
        work_dir.mkdir(parents=True, exist_ok=True)
        round_run_root = run_root_from_path(round_worktree, main_workspace_root)
        if round_run_root != provided_run_root:
            raise SystemExit(
                "round worktree and --round-work-dir must belong to the same controller run root: "
                f"round_worktree={round_worktree}, round_work_dir={work_dir}"
            )
    else:
        round_run_root = run_root_from_path(round_worktree, main_workspace_root)
        if round_run_root is None:
            raise SystemExit(
                f"round worktree must be under {main_workspace_root / 'worktrees'}/<case>-YYYYMMDDHHMMSS/: "
                f"{round_worktree}"
            )
        expected_round_name = args.vc_proving_round_id or round_worktree.name
        work_dir = reports_root(round_run_root) / "rounds" / expected_round_name
        work_dir.mkdir(parents=True, exist_ok=True)

    manual_rel = relative_to_worktree(manual_path, round_worktree)
    case_lib_rel = relative_to_worktree(case_lib, round_worktree)
    if manual_rel is None or case_lib_rel is None:
        raise SystemExit("proof manual and case_lib must be below the round worktree root")
    run_root = run_root_from_path(work_dir, main_workspace_root)
    if run_root is None:
        raise SystemExit(f"round report directory is not under a controller report root: {work_dir}")
    round_run_root = run_root_from_path(round_worktree, main_workspace_root)
    if round_run_root != run_root:
        raise SystemExit(
            "round worktree and round report directory must belong to the same controller run root: "
            f"round_worktree={round_worktree}, work_dir={work_dir}"
        )
    report_root = reports_root(run_root)
    round_reports = work_dir
    round_case_dir = manual_path.parent
    coq_config = infer_case_config(round_worktree, round_case_dir)
    diagnostics_path = diagnostics_file_for_manual(manual_rel)
    diagnostics_snapshot_path = diagnostics_snapshot_for_manual(manual_rel)

    manifest = {
        "schema_version": "qcp-vc-proving-group-workers-manifest/v1",
        "manifest_kind": "group-workers-manifest",
        "vc_proving_round_id": args.vc_proving_round_id or work_dir.name,
        "vc_proving_container": str(run_root / (args.vc_proving_round_id or work_dir.name)),
        "round_worktree": str(round_worktree),
        "work_dir": str(work_dir),
        "run_root": str(run_root),
        "report_root": str(report_root),
        "round_report_directory": str(round_reports),
        "coq_builds_root": str(run_builds_root(run_root)),
        "proof_manual_file": str(manual_rel),
        "case_lib": str(case_lib_rel),
        "main_workspace_root": str(main_workspace_root),
        "round_coq_workspace_root": str(round_worktree),
        "case_name": coq_config["case_name"],
        "active_case_theory": coq_config["active_theory"],
        "round_case_dir": str(round_case_dir),
        "round_check_file": coq_config["check_file"],
        "proof_manual_target_file": str(manual_rel),
        "proof_diagnostics_file": str(diagnostics_path),
        "diagnostics_snapshot": str(diagnostics_snapshot_path),
        "coq_tooling": {
            "mode": "fixed-coqc-coqtop-build-workspace",
            "main_workspace_root": str(main_workspace_root),
            "coq_workspace_root": str(round_worktree),
            "helper": str(main_workspace_root / ".agents" / "skills" / "vc-proving" / "scripts" / "coq_tooling.py"),
            "fixed_flags": fixed_flags(),
            "fixed_flags_hash": fixed_flags_hash(),
            "coqc_o_allowed": "no",
            "coq_tooling_only": "yes",
            "alternate_tooling_disabled": "yes",
            "flag_retry_allowed": "no",
        },
        "source_goal_version": args.source_goal_version,
        "target_witnesses": target_names,
        "all_witnesses": lemma_names,
        "witness_statement_hashes": {
            str(lemma["name"]): {
                "statement_hash": lemma_statement_hash(lemma),
                "target_symbol": lemma_target_symbol(lemma),
            }
            for lemma in lemmas
        },
        "lemmas": [
            {
                "name": str(lemma["name"]),
                "statement_header": str(lemma["header_line"]),
                "original_start_line": int(lemma["start_line"]),
                "original_end_line": int(lemma["end_line"]),
                "statement_hash": lemma_statement_hash(lemma),
                "target_symbol": lemma_target_symbol(lemma),
            }
            for lemma in lemmas
            if str(lemma["name"]) in target_set
        ],
        "groups": [],
    }
    snapshot_abs = round_worktree / diagnostics_snapshot_path
    if snapshot_abs.is_file():
        manifest["diagnostics_snapshot_payload"] = json.loads(snapshot_abs.read_text(encoding="utf-8"))
    manifest_path = work_dir / GROUP_WORKERS_MANIFEST_NAME
    manifest["group_workers_manifest"] = str(manifest_path)
    write_json(manifest_path, manifest)
    print(f"Group workers manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
