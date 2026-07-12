#!/usr/bin/env python3
"""Create group worktrees and group-worker handoff files for vc-proving."""

from __future__ import annotations

import argparse
import json
import shlex
import shutil
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from coq_tooling import fixed_flags_hash, infer_case_config, make_coqc_argv, make_coqtop_argv
from group_plan_utils import group_entries_from_plan, load_group_plan
from proof_manual_utils import helper_namespace_for_group_id
from worktree_utils import (
    coq_identifier_slug,
    create_group_worktree,
    group_worker_spawn_message,
    init_group_worker_files,
    main_workspace_root_from_run_root,
    reports_root,
    run_builds_root,
    slug,
    write_json,
)

GROUP_WORKERS_MANIFEST_NAME = "group_workers_manifest.json"


def _formal_file_candidates(manual_rel: Path) -> list[Path]:
    stem = manual_rel.name
    candidates = [manual_rel]
    replacements = {
        "_proof_manual.v": [
            "_goal.v",
            "_proof_auto.v",
            "_goal_check.v",
            "_proof_diagnostics.v",
        ],
    }
    for suffix, generated_suffixes in replacements.items():
        if stem.endswith(suffix):
            base = stem[: -len(suffix)]
            candidates.extend(manual_rel.with_name(base + item) for item in generated_suffixes)
            candidates.append(manual_rel.with_name("diagnostics_snapshot.json"))
            break
    return candidates


def _sync_round_files(round_worktree: Path, group_worktree: Path, manifest: dict[str, Any]) -> None:
    rels = set(_formal_file_candidates(Path(str(manifest["proof_manual_file"]))))
    rels.add(Path(str(manifest["case_lib"])))
    for rel in rels:
        src = round_worktree / rel
        if not src.is_file():
            continue
        dest = group_worktree / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dest)


def _render_group_worker_instructions(group: dict[str, Any], manifest: dict[str, Any]) -> str:
    report_dir = group.get("group_report_directory", "<group-report-directory>")
    return group_worker_spawn_message(
        Path(str(report_dir)) / "group_worker_input.json",
        Path(str(report_dir)) / "group_worker_report.json",
    )


def _round_agent_input_context(work_dir: Path) -> dict[str, Any]:
    input_path = work_dir / "agent_input.json"
    if not input_path.is_file():
        return {}
    try:
        payload = json.loads(input_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, dict) else {}


def _difficulty_score(group: dict[str, Any], manifest: dict[str, Any]) -> float:
    raw = group.get("difficulty")
    if isinstance(raw, (int, float)):
        return float(raw)
    if isinstance(raw, str):
        lowered = raw.strip().lower()
        if lowered in {"hard", "high"}:
            return 10.0
        if lowered in {"medium", "med"}:
            return 5.0
        if lowered in {"easy", "low"}:
            return 1.0
        try:
            return float(lowered)
        except ValueError:
            pass
    score = float(len(group.get("witness_names", [])))
    helpers = group.get("candidate_helper_declarations")
    if not isinstance(helpers, list):
        helpers = group.get("expected_helpers") if isinstance(group.get("expected_helpers"), list) else []
    score += 2.0 * len(helpers)
    if group.get("refinement_plan"):
        score += 2.0
    diagnostics = manifest.get("diagnostics_snapshot_payload")
    if isinstance(diagnostics, dict):
        by_witness = diagnostics.get("by_witness") if isinstance(diagnostics.get("by_witness"), dict) else {}
        for witness in group.get("witness_names", []):
            split_goals = by_witness.get(str(witness), {}).get("split_goals") if isinstance(by_witness.get(str(witness)), dict) else []
            if isinstance(split_goals, list):
                score += 0.5 * len(split_goals)
    score += float(len(group.get("dependencies", [])))
    return score


def _require_under(name: str, path: Path, root: Path) -> None:
    resolved = path.expanduser().resolve()
    root_resolved = root.expanduser().resolve()
    try:
        resolved.relative_to(root_resolved)
    except ValueError:
        raise SystemExit(f"{name} must be under {root_resolved}: {resolved}")


def _require_equal(name: str, actual: Path, expected: Path) -> None:
    actual_resolved = actual.expanduser().resolve()
    expected_resolved = expected.expanduser().resolve()
    if actual_resolved != expected_resolved:
        raise SystemExit(f"{name} must be {expected_resolved}: {actual_resolved}")


def _dependency_ready_order(groups: list[dict[str, Any]]) -> list[str]:
    remaining = {str(group["group_id"]): group for group in groups}
    accepted: set[str] = set()
    order: list[str] = []
    while remaining:
        ready = [
            group
            for group in remaining.values()
            if all(str(dep) in accepted for dep in group.get("dependencies", []))
        ]
        if not ready:
            order.extend(sorted(remaining))
            break
        ready.sort(
            key=lambda group: (
                float(group.get("estimated_difficulty_score", 0.0) or 0.0),
                len(group.get("witness_names", [])),
                str(group.get("group_id")),
            ),
            reverse=True,
        )
        for group in ready:
            group_id = str(group["group_id"])
            order.append(group_id)
            accepted.add(group_id)
            remaining.pop(group_id, None)
    return order


def prepare_group_worktrees(
    manifest_path: Path,
    *,
    group_plan_path: Path | None = None,
    force_group_worktrees: bool = False,
    group_worktree_root: Path | None = None,
    max_compact_attempts: int = 3,
) -> list[dict[str, Any]]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict):
        raise SystemExit("manifest must be a JSON object")
    round_worktree = Path(str(manifest["round_worktree"])).resolve()
    work_dir = Path(str(manifest["work_dir"])).resolve()
    round_input_context = _round_agent_input_context(work_dir)
    if "problem_context" not in manifest and isinstance(round_input_context.get("problem_context"), dict):
        manifest["problem_context"] = round_input_context["problem_context"]
    if "annotation_design_summary" not in manifest and isinstance(round_input_context.get("annotation_design_summary"), dict):
        manifest["annotation_design_summary"] = round_input_context["annotation_design_summary"]
    if not manifest.get("main_workspace_root"):
        raise SystemExit("manifest.main_workspace_root is required so group Coq tooling uses the main worktree helper")
    if not manifest.get("source_goal_version"):
        raise SystemExit("manifest.source_goal_version is required before preparing group-worker Coq handoff")
    if not manifest.get("run_root"):
        raise SystemExit("manifest.run_root is required; group worktrees must be bound to a controller run root")
    main_workspace_root = Path(str(manifest["main_workspace_root"])).resolve()
    case_name = str(manifest.get("case_name") or Path(str(manifest["proof_manual_file"])).parent.name)
    run_root = Path(str(manifest["run_root"])).resolve()
    _require_equal("manifest.main_workspace_root", main_workspace_root, main_workspace_root_from_run_root(run_root))
    _require_under("manifest.round_worktree", round_worktree, run_root)
    vc_proving_round_id = str(manifest.get("vc_proving_round_id") or work_dir.name)
    _require_equal("manifest.work_dir", work_dir, reports_root(run_root) / "rounds" / vc_proving_round_id)
    if manifest.get("round_report_directory"):
        _require_equal(
            "manifest.round_report_directory",
            Path(str(manifest["round_report_directory"])),
            work_dir,
        )
    coq_builds_root = (
        Path(str(manifest["coq_builds_root"])).resolve()
        if manifest.get("coq_builds_root")
        else run_builds_root(run_root)
    )
    _require_equal("manifest.coq_builds_root", coq_builds_root, run_builds_root(run_root))
    manifest["run_root"] = str(run_root)
    manifest["coq_builds_root"] = str(coq_builds_root)
    manifest["max_compact_attempts"] = max_compact_attempts
    lemmas = list(manifest.get("lemmas", []))
    if group_plan_path is None:
        raise SystemExit("prepare_group_worktrees requires a controller-verified --group-plan")
    group_entries = group_entries_from_plan(
        lemmas,
        load_group_plan(group_plan_path),
        require_controller_verified=True,
        source_goal_version=str(manifest.get("source_goal_version")),
    )
    group_plan_source = str(group_plan_path.resolve())
    if group_worktree_root is None:
        group_worktree_root = Path(str(manifest.get("vc_proving_container") or (run_root / vc_proving_round_id))).resolve()
    else:
        group_worktree_root = group_worktree_root.resolve()
        try:
            group_worktree_root.relative_to(run_root)
        except ValueError:
            raise SystemExit(f"--group-worktree-root must be under run root {run_root}: {group_worktree_root}")
    _require_under("group_worktree_root", group_worktree_root, run_root)
    if manifest.get("vc_proving_container"):
        _require_equal("manifest.vc_proving_container", Path(str(manifest["vc_proving_container"])), group_worktree_root)
    container_slug = slug(vc_proving_round_id)
    group_manifests: list[dict[str, Any]] = []
    for index, group in enumerate(group_entries):
        estimated_difficulty_score = _difficulty_score(group, manifest)
        try:
            helper_namespace = helper_namespace_for_group_id(group["group_id"])
        except ValueError as exc:
            raise SystemExit(str(exc)) from exc
        group_worktree = create_group_worktree(
            source_worktree=round_worktree,
            group_root=group_worktree_root,
            group_id=str(group["group_id"]),
            index=index,
            force=force_group_worktrees,
        )
        _require_under("group worktree", group_worktree, group_worktree_root)
        _require_under("group worktree", group_worktree, run_root)
        group_reports = work_dir / "groups" / slug(group_worktree.name)
        group_reports.mkdir(parents=True, exist_ok=True)
        _require_under("group report directory", group_reports, reports_root(run_root))
        _sync_round_files(round_worktree, group_worktree, manifest)
        manual_rel = Path(str(manifest["proof_manual_file"]))
        case_name = str(manifest.get("case_name") or manual_rel.name[: -len("_proof_manual.v")])
        group_check_rel = (
            Path(".coq_group_checks")
            / f"{case_name}_group_{index:02d}__{coq_identifier_slug(group['group_id'])}_check.v"
        )
        debug_rel = Path(".coq_debug") / f"group_{index:02d}__{slug(group['group_id'])}.v"
        group_case_dir = group_worktree / manual_rel.parent
        group_coq_config = infer_case_config(group_worktree, group_case_dir)
        group_build_workspace = coq_builds_root / container_slug / f"group_{index:02d}__{slug(group['group_id'])}" / "src"
        _require_under("group coq build workspace", group_build_workspace, coq_builds_root)
        _require_under("group coq build workspace", group_build_workspace, run_root)
        helper_script = main_workspace_root / ".agents" / "skills" / "vc-proving" / "scripts" / "coq_tooling.py"
        coq_tooling_check_argv = [
            "python3",
            str(helper_script),
            "check",
            "--workspace-root",
            str(group_worktree),
            "--build-workspace",
            str(group_build_workspace),
            "--target-file",
            group_check_rel.as_posix(),
            "--target-kind",
            "group-check",
            "--source-goal-version",
            str(manifest["source_goal_version"]),
            "--group-check-case-theory",
            str(group_coq_config.get("active_theory")),
            "--group-check-require",
            case_name + "_goal",
            "--group-check-require",
            case_name + "_proof_auto",
            "--group-check-require",
            case_name + "_proof_manual",
        ]
        for witness in group["witness_names"]:
            coq_tooling_check_argv.extend(["--assigned-witness", str(witness)])
        coq_tooling_debug_argv = [
            "python3",
            str(helper_script),
            "debug",
            "--workspace-root",
            str(group_worktree),
            "--build-workspace",
            str(group_build_workspace),
            "--debug-script",
            debug_rel.as_posix(),
            "--source-goal-version",
            str(manifest["source_goal_version"]),
        ]
        group_tooling = {
            "coq_tooling_only": "yes",
            "alternate_tooling_disabled": "yes",
            "coqc_o_allowed": "no",
            "flag_retry_allowed": "no",
            "coqc_check_required": "yes",
            "source_goal_version_required": "yes",
            "main_workspace_root": str(main_workspace_root),
            "coq_workspace_root": str(group_worktree),
            "coq_tooling_helper": str(helper_script),
            "coq_tooling_check_argv": coq_tooling_check_argv,
            "coq_tooling_check_command": shlex.join(coq_tooling_check_argv),
            "coq_tooling_debug_argv": coq_tooling_debug_argv,
            "coq_tooling_debug_command": shlex.join(coq_tooling_debug_argv),
            "coqc_check_argv": make_coqc_argv(group_check_rel),
            "coqtop_debug_argv": make_coqtop_argv(group_build_workspace / debug_rel),
            "coqc_check_target_file": group_check_rel.as_posix(),
            "coqtop_debug_script": debug_rel.as_posix(),
            "target_kind": "group-check",
            "group_check": {
                "case_theory": group_coq_config.get("active_theory"),
                "require_modules": [case_name + "_goal", case_name + "_proof_auto", case_name + "_proof_manual"],
                "assigned_witnesses": [str(name) for name in group["witness_names"]],
            },
            "fixed_flags_hash": fixed_flags_hash(),
            "group_case_dir": str(group_case_dir),
            "group_active_case_theory": group_coq_config.get("active_theory"),
            "coq_build_workspace": str(group_build_workspace),
            "parent_round_check_file": manifest.get("round_check_file"),
            "full_check_required_before_parent_acceptance": "yes",
            "proof_manual_check_allowed": "no",
            "proof_manual_check_reason": "worker group evidence must use build-workspace-only group-check; parent verify runs full goal_check",
        }
        group_for_instructions = {
            **group,
            "worktree_path": str(group_worktree),
            "group_report_directory": str(group_reports),
            "tooling": group_tooling,
            "estimated_difficulty_score": estimated_difficulty_score,
        }
        vc_checking_plan = {
            "group_entry": group.get("vc_checking_group_entry", {}),
            "per_witness_plan": group.get("per_witness_plan", {}),
            "vc_shape": group.get("vc_shape", {}),
            "witness_instantiation": group.get("witness_instantiation", {}),
            "space_plan": group.get("space_plan", {}),
            "pure_plan": group.get("pure_plan", {}),
            "refinement_plan": group.get("refinement_plan", {}),
            "candidate_helper_declarations": group.get("candidate_helper_declarations", []),
            "premise_discharge": group.get("premise_discharge", {}),
            "fallback_policy": "if plan fields are missing or weak, analyze assigned witnesses locally in this same spawn",
        }
        group_manifest = {
            "schema_version": "qcp-vc-proving-group-manifest/v1",
            "group_id": str(group["group_id"]),
            "index": index,
            "worktree_path": str(group_worktree),
            "handoff_files": {
                "input": str(group_reports / "group_worker_input.json"),
                "report": str(group_reports / "group_worker_report.json"),
                "output": str(group_reports / "group_worker_output.txt"),
            },
            "startup": {
                "owner": "main-agent",
                "method": "main-agent-worker-attempt",
                "script_launch_allowed": "no",
                "resume_policy": {
                    "on_compact_error": "main-agent-restarts-worker",
                    "attempt_index": 1,
                    "max_compact_attempts": max_compact_attempts,
                    "when_exhausted": "return-blocked-with-compact-error-retry-exhausted",
                    "previous_attempt_reference": str(group_worktree),
                },
            },
            "spawn": {
                "namespace": "multi_agent_v1",
                "tool": "spawn_agent",
                "fork_context": False,
                "fork_turns": "none",
                "parent_context_allowed": False,
            },
            "round_worktree": str(round_worktree),
            "proof_manual_file": manifest["proof_manual_file"],
            "case_lib": manifest["case_lib"],
            "source_goal_version": manifest.get("source_goal_version"),
            "problem_context": manifest.get("problem_context", {}),
            "annotation_design_summary": manifest.get("annotation_design_summary", {}),
            "helper_namespace": helper_namespace,
            "tooling": group_tooling,
            "witness_names": group["witness_names"],
            "dependencies": group.get("dependencies", []),
            "estimated_difficulty_score": estimated_difficulty_score,
            "representative_witness": group.get("representative_witness"),
            "proof_strategy": group.get("proof_strategy", ""),
            "expected_helpers": group.get("expected_helpers", []),
            "vc_checking_plan": vc_checking_plan,
            "group_plan_source": group_plan_source,
        }
        group_worker_input = {
            **group_manifest,
            "handoff": {
                "rendered_instructions_compact": _render_group_worker_instructions(group_for_instructions, manifest),
                "detailed_rules": {
                    "skill_docs": [
                        ".agents/skills/group-worker-proving/SKILL.md",
                        ".agents/skills/group-worker-proving/docs/coq-tooling-policy.md",
                        ".agents/skills/group-worker-proving/docs/separation-logic-whole-proof-tactics.md",
                        ".agents/skills/group-worker-proving/docs/refinement-proof-tactics.md",
                        ".agents/skills/group-worker-proving/docs/pure-proposition-proof-patterns.md",
                        ".agents/skills/group-worker-proving/docs/reference-cases.md",
                    ],
                    "assigned_witnesses": [str(name) for name in group["witness_names"]],
                    "helper_namespace": helper_namespace,
                    "formal_edit_rules": {
                        "proof_manual": "edit assigned witness proof bodies only",
                        "case_lib": (
                            "add proved helper declarations and official Rocq library imports only; "
                            "every new helper name must end with helper_namespace.suffix; "
                            "new imports must be Require Import Coq.* or From Coq... Require Import ..."
                        ),
                        "generated_files": "read-only",
                    },
                    "forbidden_tools": ["jq"],
                },
            },
        }
        init_group_worker_files(
            group_worktree=group_worktree,
            report_dir=group_reports,
            group_id=str(group["group_id"]),
            assigned_witnesses=[str(name) for name in group["witness_names"]],
            group_workers_manifest=manifest_path,
            group_manifest=group_worker_input,
        )
        group_manifests.append(group_manifest)
    manifest["schema_version"] = "qcp-vc-proving-group-workers-manifest/v1"
    manifest["manifest_kind"] = "group-workers-manifest"
    manifest["compact_error"] = {
        "max_compact_attempts": max_compact_attempts,
        "when_exhausted": "return-blocked-with-compact-error-retry-exhausted",
    }
    manifest["startup"] = {
        "owner": "main-agent",
        "method": "main-agent-scheduler",
        "script_launch_allowed": "no",
        "instruction": (
            "Main agent reads each group handoff file, assigns dependency-ready group-workers "
            "to available parallel slots, and starts worker attempts itself."
        ),
    }
    manifest["groups"] = group_manifests
    manifest["dependency_ready_order"] = _dependency_ready_order(group_manifests)
    manifest["scheduling_policy"] = {
        "kind": "hint-only",
        "order": "difficulty-first among dependency-ready groups",
        "acceptance_evidence": "no",
        "spawn_minimization": "vc-checking should prefer fewer, larger groups when one worker can solve them coherently",
    }
    manifest["group_workers_manifest"] = str(manifest_path)
    manifest["group_worktree_root"] = str(group_worktree_root)
    manifest["vc_proving_round_id"] = vc_proving_round_id
    manifest["vc_proving_container"] = str(group_worktree_root)
    write_json(manifest_path, manifest)
    print(f"Prepared {len(group_manifests)} group worktree(s)")
    print(f"Group workers manifest: {manifest_path}")
    return group_manifests


def load_group_workers_manifest(manifest_or_round_work_dir: Path) -> list[dict[str, Any]]:
    path = manifest_or_round_work_dir
    if path.is_dir():
        path = path / GROUP_WORKERS_MANIFEST_NAME
    payload = json.loads(path.read_text(encoding="utf-8"))
    groups = payload.get("groups") if isinstance(payload, dict) else None
    if not isinstance(groups, list):
        raise SystemExit(f"invalid group workers manifest: {path}")
    return groups


def main() -> int:
    parser = argparse.ArgumentParser(description="Create vc-proving group Git worktrees and handoff files.")
    parser.add_argument("manifest", help="Path to group_workers_manifest.json from init_vc_proving_round.py")
    parser.add_argument("--group-plan", default=None, help="Strict vc-checking group plan JSON")
    parser.add_argument("--force-group-worktrees", action="store_true", help="Replace existing group worktrees")
    parser.add_argument(
        "--group-worktree-root",
        default=None,
        help="Group worktree root; defaults to <run-root>/<case>-vc-proving-rN",
    )
    parser.add_argument("--max-compact-attempts", type=int, default=3)
    args = parser.parse_args()
    prepare_group_worktrees(
        Path(args.manifest).expanduser().resolve(),
        group_plan_path=Path(args.group_plan).expanduser().resolve() if args.group_plan else None,
        force_group_worktrees=args.force_group_worktrees,
        group_worktree_root=Path(args.group_worktree_root).expanduser().resolve() if args.group_worktree_root else None,
        max_compact_attempts=args.max_compact_attempts,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
