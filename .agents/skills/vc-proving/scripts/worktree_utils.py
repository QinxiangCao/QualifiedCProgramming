#!/usr/bin/env python3
"""Filesystem helpers for vc-proving round/group worktrees.

This module intentionally stays below the vc-proving script layer.  It creates
and annotates Git worktrees, but it does not own phase transitions, terminal
decisions, or main-worktree adoption.
"""

from __future__ import annotations

import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


GROUP_WORKER_FILE_SET = (
    "group_worker_input.json",
    "group_worker_report.json",
    "group_worker_output.txt",
)
WORKTREE_ROOT_NAME = "worktrees"
RUN_BUILDS_DIR_NAME = "_coq_builds"
REPORTS_DIR_NAME = "reports"
RUN_ROOT_RE = re.compile(r"^.+-\d{14}(?:-\d{2})?$")


def group_worker_spawn_message(input_path: Path | str, report_path: Path | str) -> str:
    return "\n".join(
        [
            f"Read {input_path}.",
            f"The goal is to complete the group-worker task assigned by group_worker_input.json; {report_path} is only the final report file recording the result.",
            "Before acting, read group_worker_input.json completely and read every skill or rule file listed under handoff.detailed_rules.skill_docs.",
            "The group_worker_input.json, group_workers_manifest.json, declared group worktree, declared source_goal_version, and current files are the source of truth.",
            "Do not rely on parent chat history or unstated assumptions as task context or evidence.",
            "Minimize respawns: solve every assigned witness in this group inside this same spawn whenever the source_goal_version and helper namespace are still current.",
            "Do not stop for confirmation about proof uncertainty, missing optional hints, or a failed tactic; inspect the proof state, try an alternate route, add current-suffix helpers when useful, and re-run the fixed group check.",
            "Work only in the declared group worktree; write only the declared group_worker_report.json, group_worker_output.txt, assigned witness proof bodies, current group-suffixed case_lib helpers, and official Rocq library imports needed by those proofs.",
            "No compromise operations: do not weaken specifications, bypass required checks, fake evidence, change generated files by hand, change witness statements, edit unassigned witnesses, edit seed case_lib declarations, add unsuffixed or foreign-suffix helpers, add non-Rocq/project/generated case_lib imports, add Admitted/Axiom, or use forbidden tools/tactics.",
            "Task completion means the assigned group proof work is completed under the strict workflow, with a terminal group status, solved/unsolved witnesses, blockers or errors, changed-files details, helper/import declarations, source_goal_version-bound Coq evidence, and an output note satisfying output_contract.",
            "Controller/parent verification acceptance is separate; do not claim group acceptance or final proof acceptance unless the controller writes it.",
            "Reuse only references explicitly declared in group_worker_input.json; previous output notes are non-authoritative and lose conflicts to JSON, manifests, source versions, and current files.",
            "Compact-error is not your blocked judgment; report it only as a compaction fact and let controller/main decide retry or final blocker.",
            "If the strict workflow cannot be completed, write a blocked, stale, or compact-error result with concrete evidence instead of improvising around the process.",
        ]
    )


def slug(value: object) -> str:
    text = re.sub(r"[^A-Za-z0-9_.-]+", "-", str(value).strip())
    text = text.strip("-._")
    return text or "unnamed"


def coq_identifier_slug(value: object) -> str:
    text = re.sub(r"[^A-Za-z0-9_]+", "_", str(value).strip())
    text = re.sub(r"_+", "_", text).strip("_")
    if not text:
        return "unnamed"
    if text[0].isdigit():
        return "_" + text
    return text


def git(repo: Path, args: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=check,
    )


def git_toplevel(start: Path) -> Path:
    start = start.resolve()
    cwd = start if start.is_dir() else start.parent
    proc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise SystemExit(f"not inside a Git worktree: {start}\n{proc.stderr.strip()}")
    return Path(proc.stdout.strip()).resolve()


def relative_to_worktree(path: Path, worktree: Path) -> Path | None:
    try:
        return path.resolve().relative_to(worktree.resolve())
    except ValueError:
        return None


def case_name_from_formal_path(path: Path) -> str:
    parent = path.resolve().parent if path.suffix else path.resolve()
    return slug(parent.name)


def is_run_root_name(name: str) -> bool:
    return RUN_ROOT_RE.match(name) is not None


def run_root_from_path(path: Path, main_workspace_root: Path) -> Path | None:
    resolved = path.expanduser().resolve()
    main = main_workspace_root.expanduser().resolve()
    for root_name in (WORKTREE_ROOT_NAME, REPORTS_DIR_NAME):
        try:
            rel = resolved.relative_to(main / root_name)
        except ValueError:
            continue
        if not rel.parts:
            continue
        candidate = main / WORKTREE_ROOT_NAME / rel.parts[0]
        if is_run_root_name(candidate.name):
            return candidate
    return None


def main_workspace_root_from_run_root(run_root: Path) -> Path:
    run_root = run_root.expanduser().resolve()
    if run_root.parent.name != WORKTREE_ROOT_NAME:
        raise SystemExit(f"run root must be under <main-worktree-root>/{WORKTREE_ROOT_NAME}: {run_root}")
    return run_root.parent.parent.resolve()


def utc_timestamp() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def ensure_run_root(
    main_workspace_root: Path,
    case_name: str,
    *,
    path_hint: Path | None = None,
    timestamp: str | None = None,
) -> Path:
    main_workspace_root = main_workspace_root.expanduser().resolve()
    if path_hint is not None:
        existing = run_root_from_path(path_hint, main_workspace_root)
        if existing is not None:
            (existing / RUN_BUILDS_DIR_NAME).mkdir(parents=True, exist_ok=True)
            reports_root(existing)
            return existing
    stamp = timestamp or datetime.now().strftime("%Y%m%d%H%M%S")
    base_name = f"{slug(case_name)}-{stamp}"
    parent = main_workspace_root / WORKTREE_ROOT_NAME
    parent.mkdir(parents=True, exist_ok=True)
    run_root = parent / base_name
    suffix = 1
    while run_root.exists() and any(run_root.iterdir()):
        run_root = parent / f"{base_name}-{suffix:02d}"
        suffix += 1
    run_root.mkdir(parents=True, exist_ok=True)
    (run_root / RUN_BUILDS_DIR_NAME).mkdir(parents=True, exist_ok=True)
    reports_root(run_root)
    return run_root.resolve()


def run_builds_root(run_root: Path) -> Path:
    path = run_root.expanduser().resolve() / RUN_BUILDS_DIR_NAME
    path.mkdir(parents=True, exist_ok=True)
    return path


def reports_root(run_root: Path) -> Path:
    run_root = run_root.expanduser().resolve()
    path = main_workspace_root_from_run_root(run_root) / REPORTS_DIR_NAME / run_root.name
    path.mkdir(parents=True, exist_ok=True)
    return path


def run_status_path(run_root: Path) -> Path:
    return reports_root(run_root) / "run_status.json"


def run_events_path(run_root: Path) -> Path:
    return reports_root(run_root) / "run_events.json"


def run_logs_path(run_root: Path) -> Path:
    return reports_root(run_root) / "run_logs.json"


def round_report_root(run_root: Path, round_worktree: Path) -> Path:
    path = reports_root(run_root) / "rounds" / slug(round_worktree.name)
    path.mkdir(parents=True, exist_ok=True)
    return path


def default_round_workspace(
    repo_root: Path,
    manual_file: Path,
    *,
    main_workspace_root: Path | None = None,
    timestamp: str | None = None,
) -> Path:
    case_name = case_name_from_formal_path(manual_file)
    owner_root = main_workspace_root if main_workspace_root is not None else repo_root
    run_root = ensure_run_root(owner_root, case_name, path_hint=repo_root, timestamp=timestamp)
    return round_report_root(run_root, repo_root)


def next_numbered_dir(parent: Path, stem: str) -> Path:
    parent.mkdir(parents=True, exist_ok=True)
    index = 0
    while True:
        candidate = parent / f"{slug(stem)}__{index:02d}"
        if not candidate.exists():
            candidate.mkdir(parents=True)
            return candidate.resolve()
        index += 1


def create_group_worktree(
    *,
    source_worktree: Path,
    group_root: Path,
    group_id: str,
    index: int,
    force: bool = False,
) -> Path:
    """Create a detached group Git worktree from the current round worktree."""
    source_worktree = git_toplevel(source_worktree)
    group_root = group_root.resolve()
    group_root.mkdir(parents=True, exist_ok=True)
    path = group_root / f"group_{index:02d}__{slug(group_id)}"
    if path.exists():
        if not force:
            raise SystemExit(
                f"group worktree already exists: {path}; pass --force-group-worktrees to replace it"
            )
        git(source_worktree, ["worktree", "remove", "--force", str(path)], check=False)
    git(source_worktree, ["worktree", "add", "--detach", str(path), "HEAD"])
    return path.resolve()


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")


def build_group_worker_input_payload(
    *,
    group_worktree: Path,
    report_dir: Path,
    group_id: str,
    assigned_witnesses: list[str],
    group_workers_manifest: Path,
    group_manifest: dict[str, Any],
) -> dict[str, Any]:
    startup = group_manifest.get("startup") if isinstance(group_manifest.get("startup"), dict) else {}
    resume_policy = startup.get("resume_policy") if isinstance(startup.get("resume_policy"), dict) else {}
    helper_namespace = (
        group_manifest.get("helper_namespace")
        if isinstance(group_manifest.get("helper_namespace"), dict)
        else {}
    )
    max_compact_attempts = int(resume_policy.get("max_compact_attempts", 3))
    attempt_index = int(resume_policy.get("attempt_index", 1))
    attempt_id = f"{group_id}-attempt-{attempt_index}"
    return {
        "schema_version": "qcp-group-worker-input/v1",
        "group": {
            "group_id": group_id,
            "assigned_witnesses": assigned_witnesses,
            "worktree_path": str(group_worktree.resolve()),
        },
        "attempt_control": {
            "attempt_id": attempt_id,
            "attempt_index": attempt_index,
            "max_compact_attempts": max_compact_attempts,
            "retry_reasons": [
                "explicit-cancel",
                "stale-input",
                "invalid-report",
                "compact-error-with-no-progress",
            ],
            "heartbeat_policy": "no-timeout-retry",
            "on_compact_error": "main-agent-restarts-worker",
            "when_exhausted": "return-blocked-with-compact-error-retry-exhausted",
            "previous_attempt_reference": str(group_worktree.resolve()),
        },
        "helper_namespace": helper_namespace,
        "single_spawn_policy": {
            "preferred": "yes",
            "goal": "complete all assigned witnesses in one worker spawn",
            "continue_without_confirmation": [
                "failed tactic",
                "missing optional proof hint",
                "helper lemma uncertainty",
                "recoverable coqtop or coqc feedback",
                "proof plan mismatch that can be repaired locally",
            ],
            "retry_inside_spawn": "yes",
            "allowed_local_repairs": [
                "change assigned witness proof bodies",
                "add proved case_lib helpers ending with helper_namespace.suffix",
                "add official Rocq library imports needed by current group helpers/proofs",
                "create and rerun debug scripts under tooling.coqtop_debug_script",
                "rerun fixed group-check via tooling.coq_tooling_check_argv",
            ],
            "terminal_blocked_only_for": [
                "assigned witness statement malformed or missing",
                "required premise cannot be derived from assigned VC or current case_lib after concrete attempts",
                "fixed coq_tooling command cannot run after command evidence",
            ],
            "state_reports": {
                "stale": "report stale when source_goal_version is no longer current",
                "compact_error": "report compact-error only as a compaction fact; controller/main decides retry or final blocker",
            },
            "controller_acceptance_model": "parent verify validates merged proof after worker returns",
        },
        "startup": {
            "owner": "main-agent",
            "method": "main-agent-worker-attempt",
            "script_launch_allowed": "no",
        },
        "group_workers_manifest": str(group_workers_manifest.resolve()),
        "group_manifest": group_manifest,
        "handoff": group_manifest.get("handoff", {}) if isinstance(group_manifest.get("handoff"), dict) else {},
        "zero_context_protocol": {
            "spawn_message": group_worker_spawn_message(
                (report_dir / "group_worker_input.json").resolve(),
                (report_dir / "group_worker_report.json").resolve(),
            ),
            "parent_context_allowed": "no",
        },
        "reports": {
            "input": str((report_dir / "group_worker_input.json").resolve()),
            "report": str((report_dir / "group_worker_report.json").resolve()),
            "output": str((report_dir / "group_worker_output.txt").resolve()),
        },
        "output_contract": {
            "path": str((report_dir / "group_worker_output.txt").resolve()),
            "kind": "non-authoritative-reuse-note",
            "required": "yes",
            "acceptance_evidence": "no",
            "must_start_with": "# Reuse Note",
            "must_contain": ["Note kind: non-authoritative reuse note"],
            "conflict_rule": "json_handoff_manifest_versions_and_current_files_win",
        },
    }


def build_group_worker_report_payload(
    *,
    group_id: str,
    assigned_witnesses: list[str],
    helper_namespace: dict[str, Any],
    source_goal_version: Any,
    tooling: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": "qcp-group-worker-report/v1",
        "group_id": group_id,
        "agent_result": {
            "vc_proving": {
                "group": {
                    "status": "pending",
                    "group_id": group_id,
                    "assigned_witnesses": assigned_witnesses,
                    "helper_namespace": helper_namespace,
                    "source_goal_version": source_goal_version,
                    "solved_witnesses": [],
                    "unsolved_witnesses": assigned_witnesses,
                    "errors": [],
                    "blockers": [],
                    "candidate": {},
                    "case_lib_added_declarations": [],
                    "verification_result": {
                        "coqc_check": {
                            "status": "pending",
                            "tool": "coqc",
                            "kind": "coqc_check",
                            "argv": tooling.get("coqc_check_argv"),
                            "cwd": tooling.get("coq_build_workspace"),
                            "target_file": tooling.get("coqc_check_target_file"),
                            "target_kind": tooling.get("target_kind", "check"),
                            "fixed_flags_hash": tooling.get("fixed_flags_hash"),
                            "source_goal_version": source_goal_version,
                        },
                        "coqtop_debug": {
                            "status": "not-run",
                            "tool": "coqtop",
                            "kind": "coqtop_debug",
                            "argv": tooling.get("coqtop_debug_argv"),
                            "cwd": tooling.get("coq_build_workspace"),
                            "fixed_flags_hash": tooling.get("fixed_flags_hash"),
                            "source_goal_version": source_goal_version,
                        },
                    },
                }
            }
        },
    }


def init_group_worker_files(
    *,
    group_worktree: Path,
    report_dir: Path,
    group_id: str,
    assigned_witnesses: list[str],
    group_workers_manifest: Path,
    group_manifest: dict[str, Any],
) -> None:
    """Create the exact group-worker handoff file set in a report directory."""
    report_dir = report_dir.resolve()
    tooling = group_manifest.get("tooling") if isinstance(group_manifest.get("tooling"), dict) else {}
    helper_namespace = (
        group_manifest.get("helper_namespace")
        if isinstance(group_manifest.get("helper_namespace"), dict)
        else {}
    )
    source_goal_version = group_manifest.get("source_goal_version")
    input_payload = build_group_worker_input_payload(
        group_worktree=group_worktree,
        report_dir=report_dir,
        group_id=group_id,
        assigned_witnesses=assigned_witnesses,
        group_workers_manifest=group_workers_manifest,
        group_manifest=group_manifest,
    )
    report_payload = build_group_worker_report_payload(
        group_id=group_id,
        assigned_witnesses=assigned_witnesses,
        helper_namespace=helper_namespace,
        source_goal_version=source_goal_version,
        tooling=tooling,
    )
    write_json(report_dir / "group_worker_input.json", input_payload)
    write_json(report_dir / "group_worker_report.json", report_payload)
    (report_dir / "group_worker_output.txt").write_text("", encoding="utf-8")


def group_worker_report_status(report_path: Path) -> dict[str, Any] | None:
    if not report_path.is_file():
        return None
    try:
        payload = json.loads(report_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    if not isinstance(payload, dict):
        return None
    return payload
