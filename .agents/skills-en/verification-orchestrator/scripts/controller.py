#!/usr/bin/env python3
"""Controller CLI for QCP verification runs.

The controller owns durable run-log state, append-only events, and main-owned
acceptance records. It never launches subagents or workers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parents[1] / "vc-proving" / "scripts"
sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from group_plan_utils import group_entries_from_plan, load_group_plan
from coq_tooling import fixed_flags_hash
from proof_manual_utils import (
    ensure_unique_lemma_names,
    lemma_statement_hash,
    lemma_target_symbol,
    manual_diagnostic_errors,
    parse_manual_file,
    write_split_manual_artifacts,
)
from worktree_utils import (
    REPORTS_DIR_NAME,
    RUN_BUILDS_DIR_NAME,
    ensure_run_root,
    git_toplevel,
    reports_root,
    run_builds_root,
    run_logs_path,
    run_status_path,
    slug,
    write_json,
)


SCHEMA_STATE = "qcp-controller-run-state/v1"
SCHEMA_RUN_LOG = "qcp-controller-run-log/v1"
SCHEMA_TIMING_SUMMARY = "qcp-timing-summary/v2"
RETRY_REASONS = {
    "explicit-cancel",
    "stale-input",
    "invalid-report",
    "compact-error-with-no-progress",
}
CANONICAL_INCLUDE = "QCP_examples/QCP_demos_LLM/"
CANONICAL_SLP = ["QCP_examples/QCP_demos_LLM/", "SimpleC.EE.QCP_demos_LLM"]
SELF_REWORKABLE_FAILURE_CLASSES = [
    "spec-quality",
    "qcp-symbolic-execution",
    "case_lib-coqc",
    "where-instantiation",
    "annotation-checking-failed",
]
DEFAULT_SELF_REPAIR_BUDGET = {
    "min_complete_cycles": 3,
    "min_wall_clock_minutes": 30,
}
DEFAULT_MAX_PARALLEL_GROUP_WORKERS = 4
DEFAULT_MAX_WITNESSES_PER_GROUP = 12
VC_PROVING_PREPARING_PHASE = "vc-proving-preparing"
VC_PROVING_LEGACY_PHASE = "vc-proving"
VC_PROVING_PHASE_ALIASES = {VC_PROVING_PREPARING_PHASE, VC_PROVING_LEGACY_PHASE}
PROBLEM_CONTEXT_FIELDS = {
    "problem_statement": "",
    "target_function": "",
    "expected_behavior": "",
    "input_output_contract": "",
    "spec_hint": [],
    "preferred_hidden_properties": [],
    "forbidden_patterns": [],
    "reference_case_hints": [],
}
GENERATED_FILE_ROLES = {
    "goal_file": "generated-goal",
    "proof_auto_file": "generated-proof-auto",
    "proof_manual_file": "generated-proof-manual",
    "goal_check_file": "generated-goal-check",
    "proof_diagnostics_file": "generated-diagnostics",
    "diagnostics_snapshot": "generated-diagnostics-snapshot",
}


def _utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _utc_timing() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z")


def _json_load(path: Path, default: Any | None = None) -> Any:
    if not path.is_file():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _problem_context_from_args(args: argparse.Namespace) -> dict[str, Any]:
    statement_parts: list[str] = []
    if getattr(args, "problem_statement", None):
        statement_parts.append(str(args.problem_statement))
    statement_file = getattr(args, "problem_statement_file", None)
    if statement_file:
        path = Path(statement_file).expanduser().resolve()
        if not path.is_file():
            raise SystemExit(f"problem statement file not found: {path}")
        statement_parts.append(path.read_text(encoding="utf-8"))
    context = {
        "problem_statement": "\n\n".join(part.strip() for part in statement_parts if part.strip()),
        "target_function": str(getattr(args, "target_function", "") or ""),
        "expected_behavior": str(getattr(args, "expected_behavior", "") or ""),
        "input_output_contract": str(getattr(args, "input_output_contract", "") or ""),
        "spec_hint": [str(item) for item in getattr(args, "spec_hint", []) or []],
        "preferred_hidden_properties": [
            str(item) for item in getattr(args, "preferred_hidden_property", []) or []
        ],
        "forbidden_patterns": [str(item) for item in getattr(args, "forbidden_pattern", []) or []],
        "reference_case_hints": [str(item) for item in getattr(args, "reference_case_hint", []) or []],
    }
    has_user_input = any(
        bool(value) if not isinstance(value, list) else bool(value)
        for value in context.values()
    )
    context["source"] = "user-input" if has_user_input else "empty-user-input"
    return context


def _normalized_problem_context(state: dict[str, Any]) -> dict[str, Any]:
    raw = state.get("problem_context") if isinstance(state.get("problem_context"), dict) else {}
    context: dict[str, Any] = {}
    for key, default in PROBLEM_CONTEXT_FIELDS.items():
        value = raw.get(key, default)
        if isinstance(default, list):
            context[key] = [str(item) for item in value] if isinstance(value, list) else []
        else:
            context[key] = str(value or "")
    context["source"] = str(raw.get("source") or "empty-user-input")
    return context


def _relative_path_for_digest(path: Path, workspace_root: Path | None) -> str:
    resolved = path.expanduser().resolve()
    if workspace_root is not None:
        try:
            return resolved.relative_to(workspace_root.expanduser().resolve()).as_posix()
        except ValueError:
            pass
    return path.as_posix() if not path.is_absolute() else path.name


def _source_version(
    paths: list[Path],
    *,
    workspace_root: Path | None = None,
    roles: dict[str, str] | None = None,
) -> dict[str, Any]:
    files: list[dict[str, Any]] = []
    digest_files: list[dict[str, Any]] = []
    for path in paths:
        resolved = path.expanduser().resolve()
        relative_path = _relative_path_for_digest(path, workspace_root)
        state = "present" if resolved.is_file() else "missing"
        role = (roles or {}).get(relative_path)
        entry: dict[str, Any] = {
            "path": str(resolved),
            "relative_path": relative_path,
            "sha256": _file_digest(resolved) if state == "present" else None,
            "state": state,
        }
        if role:
            entry["role"] = role
        files.append(entry)
        digest_entry = {
            "relative_path": entry["relative_path"],
            "sha256": entry["sha256"],
            "state": entry["state"],
        }
        if role:
            digest_entry["role"] = role
        digest_files.append(digest_entry)
    digest_files.sort(key=lambda item: (str(item.get("relative_path")), str(item.get("role", ""))))
    digest = hashlib.sha256(json.dumps(digest_files, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()
    return {
        "schema_version": "qcp-source-version/v1",
        "digest": digest,
        "digest_input_policy": "relative_path+sha256+state+role only",
        "files": files,
    }


def _target_rel_from_state(state: dict[str, Any]) -> str:
    main_root = Path(str(state["main_worktree"]))
    return _relative_path_for_digest(Path(str(state["target_c_file"])), main_root)


def _target_files_for_rel(target_rel: str) -> dict[str, str]:
    target_path = Path(target_rel)
    case_name = target_path.stem
    if target_path.parts and target_path.parts[0] == "QCP_examples":
        logical_parts = target_path.parts[1:-1]
    else:
        logical_parts = target_path.parts[:-1]
    formal_dir = Path("SeparationLogic") / "examples" / Path(*logical_parts)
    active_case_theory = "SimpleC.EE." + ".".join(logical_parts) if logical_parts else "SimpleC.EE"
    return {
        "c_file": target_path.as_posix(),
        "formal_directory": formal_dir.as_posix(),
        "case_lib": (formal_dir / f"{case_name}_lib.v").as_posix(),
        "goal_file": (formal_dir / f"{case_name}_goal.v").as_posix(),
        "proof_auto_file": (formal_dir / f"{case_name}_proof_auto.v").as_posix(),
        "proof_manual_file": (formal_dir / f"{case_name}_proof_manual.v").as_posix(),
        "goal_check_file": (formal_dir / f"{case_name}_goal_check.v").as_posix(),
        "proof_diagnostics_file": (formal_dir / f"{case_name}_proof_diagnostics.v").as_posix(),
        "diagnostics_snapshot": (formal_dir / "diagnostics_snapshot.json").as_posix(),
        "case_name": case_name,
        "active_case_theory": active_case_theory,
    }


def _target_files_for_state(state: dict[str, Any]) -> dict[str, str]:
    return _target_files_for_rel(_target_rel_from_state(state))


def _source_version_for_workspace(
    state: dict[str, Any],
    workspace_root: Path,
    *,
    annotated: bool,
) -> dict[str, Any]:
    target_files = _target_files_for_state(state)
    roles = {
        target_files["c_file"]: "target-c-annotated" if annotated else "target-c",
        target_files["case_lib"]: "case-lib-seed",
    }
    paths = [workspace_root / target_files["c_file"], workspace_root / target_files["case_lib"]]
    return _source_version(paths, workspace_root=workspace_root, roles=roles)


def _ensure_case_lib_seed(worktree_path: Path, target_files: dict[str, str]) -> dict[str, Any]:
    case_lib = worktree_path / target_files["case_lib"]
    if case_lib.is_file():
        return {
            "status": "existing",
            "path": str(case_lib.resolve()),
            "relative_path": target_files["case_lib"],
            "created": False,
            "sha256": _file_digest(case_lib),
        }
    case_lib.parent.mkdir(parents=True, exist_ok=True)
    case_lib.write_text(
        "\n".join(
            [
                "Require Import Coq.Lists.List.",
                "Require Import Coq.ZArith.ZArith.",
                "Require Import Coq.micromega.Lia.",
                "Require Import AUXLib.ListLib.",
                "",
                "Import ListNotations.",
                "Local Open Scope Z_scope.",
                "",
            ]
        ),
        encoding="utf-8",
    )
    return {
        "status": "created",
        "path": str(case_lib.resolve()),
        "relative_path": target_files["case_lib"],
        "created": True,
        "sha256": _file_digest(case_lib),
    }


def _source_goal_version_for_workspace(
    workspace_root: Path,
    target_files: dict[str, str],
) -> dict[str, Any]:
    generated_files: list[dict[str, Any]] = []
    digest_generated: list[dict[str, Any]] = []
    for key, role in GENERATED_FILE_ROLES.items():
        rel = target_files[key]
        path = workspace_root / rel
        state = "present" if path.is_file() else "missing"
        entry = {
            "relative_path": rel,
            "sha256": _file_digest(path) if state == "present" else None,
            "state": state,
            "role": role,
        }
        generated_files.append(entry)
        digest_generated.append(dict(entry))

    manual_path = workspace_root / target_files["proof_manual_file"]
    manual_text = manual_path.read_text(encoding="utf-8")
    _prelude, lemmas = parse_manual_file(manual_text)
    ensure_unique_lemma_names(lemmas)
    target_witnesses = [str(lemma["name"]) for lemma in lemmas]
    witness_statement_hashes = {str(lemma["name"]): lemma_statement_hash(lemma) for lemma in lemmas}
    witnesses = [
        {
            "name": str(lemma["name"]),
            "target_symbol": lemma_target_symbol(lemma),
            "statement_hash": lemma_statement_hash(lemma),
            "start_line": int(lemma["start_line"]),
            "end_line": int(lemma["end_line"]),
        }
        for lemma in lemmas
    ]
    digest_payload = {
        "generated_files": sorted(digest_generated, key=lambda item: (item["relative_path"], item["role"])),
        "target_witnesses": target_witnesses,
        "witness_statement_hashes": witness_statement_hashes,
    }
    digest = hashlib.sha256(
        json.dumps(digest_payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        "schema_version": "qcp-source-goal-version/v1",
        "digest": digest,
        "digest_input_policy": "relative_path+sha256+state+role over generated files and witness statements",
        "generated_files": generated_files,
        "target_witnesses": target_witnesses,
        "witness_statement_hashes": witness_statement_hashes,
        "witnesses": witnesses,
    }


def _annotation_spec_requirements(case_name: str) -> dict[str, Any]:
    generic = {
        "mathematical_postconditions_required": [
            "Function specs must state what result the function computes, not only bounds or shape facts.",
            "Loop invariants must connect processed state to the final mathematical postcondition.",
        ],
        "avoid_spec_antipatterns": [
            "Do not weaken the spec to shape-only or bounds-only conditions.",
            "Do not restate the C loops as the mathematical definition.",
            "Do not use QCP_demos_human examples.",
        ],
    }
    if case_name != "discretize":
        return generic
    return {
        "discretize_math_definition": [
            "The post-state prefix dest_map[0..ret) is strictly increasing.",
            "The post-state prefix dest_map[0..ret) contains exactly the distinct values appearing in src[0..n), with no extras and no duplicates.",
            "ret is the number of distinct values in src[0..n).",
            "Each src element maps to its rank in the sorted unique prefix; equal src values have equal ranks and smaller source values have smaller ranks.",
        ],
        "query_forward_math_definition": [
            "For a strictly increasing map[0..map_size), query_forward returns the unique index i with map[i] = target.",
            "If target does not occur in map[0..map_size), query_forward returns -1.",
        ],
        **generic,
    }


def _allowed_write_paths(phase: str, target_files: dict[str, str]) -> list[str]:
    if phase == "annotation":
        return [
            target_files["c_file"],
            target_files["case_lib"],
            target_files["goal_file"],
            target_files["proof_auto_file"],
            target_files["proof_manual_file"],
            target_files["goal_check_file"],
            target_files["proof_diagnostics_file"],
            target_files["diagnostics_snapshot"],
        ]
    if phase in VC_PROVING_PHASE_ALIASES:
        return [target_files["proof_manual_file"], target_files["case_lib"]]
    return []


def _coq_tooling_payload(
    phase: str,
    state: dict[str, Any],
    workspace_root: Path,
    target_files: dict[str, str],
) -> dict[str, Any]:
    helper = Path(str(state["main_worktree"])) / ".agents" / "skills" / "vc-proving" / "scripts" / "coq_tooling.py"
    payload = {
        "helper": str(helper),
        "main_workspace_root": str(Path(str(state["main_worktree"])).resolve()),
        "workspace_root": str(workspace_root.resolve()),
        "coq_builds_root": str(run_builds_root(Path(str(state["run_root"])))),
        "fixed_flags_hash": fixed_flags_hash(),
    }
    if phase == "annotation":
        payload["case_lib_target_kind"] = "case_lib"
        payload["round_check_file"] = target_files["goal_check_file"]
    elif phase == "vc-checking":
        payload["round_check_file"] = target_files["goal_check_file"]
    elif phase in VC_PROVING_PHASE_ALIASES:
        payload["round_check_file"] = target_files["goal_check_file"]
    return payload


def _qcp_driver_payload(state: dict[str, Any], workspace_root: Path, target_files: dict[str, str]) -> dict[str, Any]:
    main_root = Path(str(state["main_worktree"])).resolve()
    symexec = main_root / "linux-binary" / "symexec"
    return {
        "driver": str(symexec),
        "cwd": str(workspace_root.resolve()),
        "include_args": [CANONICAL_INCLUDE],
        "slp_args": list(CANONICAL_SLP),
        "coq_logic_path": target_files["active_case_theory"],
        "canonical_argv_template": [
            str(symexec),
            f"--goal-file={target_files['goal_file']}",
            f"--proof-auto-file={target_files['proof_auto_file']}",
            f"--proof-manual-file={target_files['proof_manual_file']}",
            f"-I{CANONICAL_INCLUDE}",
            "-slp",
            *CANONICAL_SLP,
            f"--coq-logic-path={target_files['active_case_theory']}",
            f"--input-file={target_files['c_file']}",
            "--no-exec-info",
        ],
    }


def _run_canonical_symexec(state: dict[str, Any], workspace_root: Path, target_files: dict[str, str]) -> dict[str, Any]:
    payload = _qcp_driver_payload(state, workspace_root, target_files)
    argv = [str(item) for item in payload["canonical_argv_template"]]
    driver = Path(argv[0])
    evidence = {
        "schema_version": "qcp-canonical-symexec-evidence/v1",
        "driver": str(driver),
        "cwd": str(workspace_root.resolve()),
        "argv": argv,
        "include_args": payload["include_args"],
        "slp_args": payload["slp_args"],
    }
    if not driver.is_file():
        return {
            **evidence,
            "status": "skipped",
            "reason": "canonical symexec driver not found in this workspace",
            "returncode": None,
            "stdout_tail": "",
            "stderr_tail": "",
        }
    if not driver.stat().st_mode & 0o111:
        return {
            **evidence,
            "status": "skipped",
            "reason": "canonical symexec driver is not executable in this workspace",
            "returncode": None,
            "stdout_tail": "",
            "stderr_tail": "",
        }
    proc = subprocess.run(
        argv,
        cwd=workspace_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    return {
        **evidence,
        "status": "passed" if proc.returncode == 0 else "failed",
        "returncode": proc.returncode,
        "stdout_tail": proc.stdout[-4000:],
        "stderr_tail": proc.stderr[-4000:],
    }


def _split_manual_diagnostics_for_workspace(workspace_root: Path, target_files: dict[str, str]) -> dict[str, Any]:
    manual_path = workspace_root / target_files["proof_manual_file"]
    split = write_split_manual_artifacts(
        manual_path,
        diagnostics_path=workspace_root / target_files["proof_diagnostics_file"],
        snapshot_path=workspace_root / target_files["diagnostics_snapshot"],
    )
    errors = manual_diagnostic_errors(manual_path.read_text(encoding="utf-8"))
    if errors:
        raise SystemExit("proof manual still contains diagnostics after split: " + "; ".join(errors))
    return {
        "status": "passed",
        "normalized_at": _utc(),
        **split,
    }


def _rules_source_for_phase(phase: str) -> list[str]:
    rules_source = [".agents/skills/verification-orchestrator/SKILL.md"]
    if phase == "annotation":
        rules_source.extend(
            [
                ".agents/skills/annotation-filling/SKILL.md",
                ".agents/skills/annotation-checking/SKILL.md",
            ]
        )
    elif phase == "vc-checking":
        rules_source.append(".agents/skills/vc-checking/SKILL.md")
    return rules_source


def _spawn_action_for_attempt(attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": f"spawn-{attempt['attempt_id']}",
        "kind": "spawn-attempt",
        "phase": attempt["phase"],
        "attempt_id": attempt["attempt_id"],
        "input": attempt["input"],
        "report": attempt["report"],
    }


def _main_owned_action(action: str, *, round_id: str, attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": f"{action}-{round_id}",
        "kind": "main-owned-action",
        "action": action,
        "phase": attempt.get("phase"),
        "round": round_id,
        "attempt_id": attempt.get("attempt_id"),
        "report": attempt.get("report"),
    }


def _round_attempt_for_phase(state: dict[str, Any], phase: str) -> tuple[str, dict[str, Any]] | tuple[None, None]:
    phases = VC_PROVING_PHASE_ALIASES if phase in VC_PROVING_PHASE_ALIASES else {phase}
    attempts = [
        (attempt_id, attempt)
        for attempt_id, attempt in state.get("attempts", {}).items()
        if isinstance(attempt, dict) and str(attempt.get("phase")) in phases and attempt.get("status") != "stale"
    ]
    if not attempts:
        return None, None
    attempts.sort(key=lambda item: _attempt_sort_key(item[1]), reverse=True)
    return attempts[0]


def _attempt_sort_key(attempt: dict[str, Any]) -> tuple[int, int]:
    round_id = str(attempt.get("round") or "")
    match = re.search(r"-r(\d+)$", round_id)
    round_index = int(match.group(1)) if match else 0
    try:
        attempt_index = int(attempt.get("attempt_index", 0))
    except (TypeError, ValueError):
        attempt_index = 0
    return round_index, attempt_index


def _next_round_id(state: dict[str, Any], phase: str) -> str:
    next_index = 1
    round_phase = VC_PROVING_LEGACY_PHASE if phase in VC_PROVING_PHASE_ALIASES else phase
    prefix = f"{slug(state['case'])}-{round_phase}-r"
    phases = VC_PROVING_PHASE_ALIASES if phase in VC_PROVING_PHASE_ALIASES else {phase}
    for attempt in state.get("attempts", {}).values():
        if not isinstance(attempt, dict) or str(attempt.get("phase")) not in phases:
            continue
        round_id = str(attempt.get("round") or "")
        if not round_id.startswith(prefix):
            continue
        suffix = round_id.rsplit("-r", 1)
        if len(suffix) == 2 and suffix[1].isdigit():
            next_index = max(next_index, int(suffix[1]) + 1)
    while f"{slug(state['case'])}-{round_phase}-r{next_index}-attempt-1" in state.get("attempts", {}):
        next_index += 1
    return f"{slug(state['case'])}-{round_phase}-r{next_index}"


def _is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.expanduser().resolve().relative_to(root.expanduser().resolve())
    except ValueError:
        return False
    return True


def _resolved_path(value: Any) -> Path | None:
    if not isinstance(value, str) or not value:
        return None
    return Path(value).expanduser().resolve()


def _same_path(left: Any, right: Any) -> bool:
    left_path = _resolved_path(left)
    right_path = _resolved_path(right)
    return left_path is not None and right_path is not None and left_path == right_path


def _current_source_goal_digest(state: dict[str, Any]) -> str | None:
    source_goal = state.get("source_goal_version")
    if isinstance(source_goal, dict):
        digest = source_goal.get("digest")
        return str(digest) if digest else None
    return str(source_goal) if source_goal else None


def _attempt_paths_valid(state: dict[str, Any], attempt: dict[str, Any]) -> bool:
    run_root = _resolved_path(state.get("run_root"))
    report_root = _resolved_path(state.get("report_root"))
    worktree = _resolved_path(attempt.get("worktree"))
    report_directory = _resolved_path(attempt.get("report_directory"))
    input_path = _resolved_path(attempt.get("input"))
    report_path = _resolved_path(attempt.get("report"))
    phase = str(attempt.get("phase") or "")
    if not run_root or not report_root or not worktree or not report_directory:
        return False
    if not _is_relative_to(worktree, run_root):
        return False
    if not _is_relative_to(report_directory, report_root):
        return False
    if phase in VC_PROVING_PHASE_ALIASES and attempt.get("controller_owned") == "yes":
        container = _resolved_path(attempt.get("container_directory"))
        if container is None or not _is_relative_to(container, run_root):
            return False
        return True
    if not input_path or not report_path:
        return False
    if not _is_relative_to(input_path, report_directory) or not _is_relative_to(report_path, report_directory):
        return False
    return True


def _current_attempt_matches(state: dict[str, Any], attempt_id: str | None, attempt: dict[str, Any] | None) -> bool:
    if not attempt_id or not isinstance(attempt, dict):
        return False
    phase = str(attempt.get("phase") or "")
    current_id, current_attempt = _round_attempt_for_phase(state, phase)
    if current_id != attempt_id or not isinstance(current_attempt, dict):
        return False
    return str(current_attempt.get("round")) == str(attempt.get("round"))


def _group_action_for_manifest_entry(round_id: str, group: dict[str, Any]) -> dict[str, Any]:
    handoff_files = group.get("handoff_files") if isinstance(group.get("handoff_files"), dict) else {}
    group_id = str(group.get("group_id"))
    return {
        "id": f"spawn-{round_id}-{group_id}",
        "kind": "spawn-group-worker",
        "phase": VC_PROVING_PREPARING_PHASE,
        "round": round_id,
        "group_id": group_id,
        "input": handoff_files.get("input"),
        "report": handoff_files.get("report"),
    }


def _manifest_path_for_attempt(attempt: dict[str, Any]) -> Path:
    return Path(str(attempt.get("report_directory", ""))) / "group_workers_manifest.json"


def _manifest_current_errors(state: dict[str, Any], attempt: dict[str, Any], manifest_path: Path, manifest: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    expected_source_goal = _current_source_goal_digest(state)
    required_fields = [
        "run_root",
        "report_root",
        "round_worktree",
        "work_dir",
        "round_report_directory",
        "main_workspace_root",
        "coq_builds_root",
        "source_goal_version",
    ]
    for field in required_fields:
        if not manifest.get(field):
            errors.append(f"manifest {field} is required")
    if expected_source_goal and manifest.get("source_goal_version") != expected_source_goal:
        errors.append("manifest source_goal_version is stale")
    if manifest.get("run_root") and not _same_path(manifest.get("run_root"), state.get("run_root")):
        errors.append("manifest run_root does not match current run")
    if manifest.get("report_root") and not _same_path(manifest.get("report_root"), state.get("report_root")):
        errors.append("manifest report_root does not match current run")
    main_worktree = _resolved_path(state.get("main_worktree"))
    if manifest.get("main_workspace_root") and main_worktree and not _same_path(manifest.get("main_workspace_root"), str(main_worktree)):
        errors.append("manifest main_workspace_root does not match current main worktree")
    if manifest.get("round_worktree") and not _same_path(manifest.get("round_worktree"), attempt.get("worktree")):
        errors.append("manifest round_worktree does not match current vc-proving-preparing source worktree")
    for key in ("work_dir", "round_report_directory"):
        if manifest.get(key) and not _same_path(manifest.get(key), attempt.get("report_directory")):
            errors.append(f"manifest {key} does not match current vc-proving-preparing report directory")
    if manifest.get("vc_proving_round_id") and str(manifest.get("vc_proving_round_id")) != str(attempt.get("round")):
        errors.append("manifest vc_proving_round_id does not match current preparing round")
    if manifest.get("vc_proving_container") and not _same_path(manifest.get("vc_proving_container"), attempt.get("container_directory")):
        errors.append("manifest vc_proving_container does not match current preparing container")
    run_root = _resolved_path(state.get("run_root"))
    if run_root and manifest.get("coq_builds_root") and not _same_path(manifest.get("coq_builds_root"), str(run_root / RUN_BUILDS_DIR_NAME)):
        errors.append("manifest coq_builds_root does not match current run _coq_builds")
    report_directory = _resolved_path(attempt.get("report_directory"))
    if report_directory and manifest_path.resolve() != (report_directory / "group_workers_manifest.json").resolve():
        errors.append("manifest path is not the current attempt manifest")
    return errors


def _manifest_groups(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    groups = manifest.get("groups") if isinstance(manifest.get("groups"), list) else []
    return [group for group in groups if isinstance(group, dict)]


def _group_entry_path_errors(
    state: dict[str, Any],
    attempt: dict[str, Any],
    group: dict[str, Any],
    *,
    require_report_pending: bool,
) -> list[str]:
    errors: list[str] = []
    run_root = _resolved_path(state.get("run_root"))
    report_root = _resolved_path(state.get("report_root"))
    attempt_report_dir = _resolved_path(attempt.get("report_directory"))
    preparing_container = _resolved_path(attempt.get("container_directory"))
    handoff_files = group.get("handoff_files") if isinstance(group.get("handoff_files"), dict) else {}
    input_path = _resolved_path(handoff_files.get("input"))
    report_path = _resolved_path(handoff_files.get("report"))
    if not run_root or not report_root or not attempt_report_dir:
        return ["current run paths are incomplete"]
    if input_path is None or report_path is None:
        errors.append("group handoff input/report path is missing")
    else:
        if not _is_relative_to(input_path, attempt_report_dir):
            errors.append("group input is outside current vc-proving report directory")
        if not _is_relative_to(report_path, attempt_report_dir):
            errors.append("group report is outside current vc-proving report directory")
        if not _is_relative_to(input_path, report_root) or not _is_relative_to(report_path, report_root):
            errors.append("group handoff paths are outside current report root")
        if not input_path.is_file() or not report_path.is_file():
            errors.append("group handoff input/report files are missing")
        elif require_report_pending and _group_report_status(report_path) != "pending":
            errors.append("group report is not pending")
    worktree_path = _resolved_path(group.get("worktree_path"))
    if worktree_path is None:
        errors.append("group worktree_path is missing")
    elif not _is_relative_to(worktree_path, run_root):
        errors.append("group worktree_path is outside current run root")
    elif preparing_container is not None and not _is_relative_to(worktree_path, preparing_container):
        errors.append("group worktree_path is outside current vc-proving-preparing container")
    tooling = group.get("tooling") if isinstance(group.get("tooling"), dict) else {}
    build_workspace = _resolved_path(tooling.get("coq_build_workspace"))
    expected_build_root = run_root / RUN_BUILDS_DIR_NAME
    if build_workspace is None:
        errors.append("group coq_build_workspace is missing")
    elif not _is_relative_to(build_workspace, expected_build_root):
        errors.append("group coq_build_workspace is outside current run _coq_builds")
    return errors


def _group_manifest_entry_for_report(
    state: dict[str, Any],
    report_path: Path,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, Path | None, list[str]]:
    attempt_id, attempt = _round_attempt_for_phase(state, VC_PROVING_PREPARING_PHASE)
    if not attempt_id or not isinstance(attempt, dict):
        return None, None, None, ["no current vc-proving-preparing attempt"]
    if not _current_attempt_matches(state, attempt_id, attempt) or not _attempt_paths_valid(state, attempt):
        return None, attempt, None, ["current vc-proving-preparing attempt paths are invalid"]
    manifest_path = _manifest_path_for_attempt(attempt)
    if not manifest_path.is_file():
        return None, attempt, manifest_path, ["current vc-proving-preparing manifest is missing"]
    manifest = _json_load(manifest_path, {})
    if not isinstance(manifest, dict):
        return None, attempt, manifest_path, ["current vc-proving-preparing manifest is invalid"]
    errors = _manifest_current_errors(state, attempt, manifest_path, manifest)
    if errors:
        return None, attempt, manifest_path, errors
    expected_report = report_path.expanduser().resolve()
    for group in _manifest_groups(manifest):
        handoff_files = group.get("handoff_files") if isinstance(group.get("handoff_files"), dict) else {}
        if _resolved_path(handoff_files.get("report")) != expected_report:
            continue
        path_errors = _group_entry_path_errors(state, attempt, group, require_report_pending=False)
        if path_errors:
            return None, attempt, manifest_path, path_errors
        return group, attempt, manifest_path, []
    return None, attempt, manifest_path, ["group report is not listed in the current vc-proving-preparing manifest"]


def _accepted_group_ids(
    state: dict[str, Any],
    *,
    round_id: str | None = None,
    source_goal_version: str | None = None,
    manifest_path: Path | None = None,
) -> set[str]:
    accepted: set[str] = set()
    manifest_text = str(manifest_path.resolve()) if manifest_path is not None else None
    for group_id, payload in state.get("group_acceptance", {}).items():
        if not isinstance(payload, dict) or payload.get("status") != "accepted":
            continue
        if round_id is not None and payload.get("round") != round_id:
            continue
        if source_goal_version is not None and payload.get("source_goal_version_digest") != source_goal_version:
            continue
        if manifest_text is not None and payload.get("manifest") != manifest_text:
            continue
        accepted.add(str(group_id))
    return accepted


def _all_manifest_groups_accepted(state: dict[str, Any], attempt: dict[str, Any]) -> bool:
    manifest_path = _manifest_path_for_attempt(attempt)
    if not manifest_path.is_file():
        return False
    manifest = _json_load(manifest_path, {})
    if not isinstance(manifest, dict) or _manifest_current_errors(state, attempt, manifest_path, manifest):
        return False
    groups = _manifest_groups(manifest)
    if not groups:
        return False
    accepted = _accepted_group_ids(
        state,
        round_id=str(attempt.get("round")),
        source_goal_version=_current_source_goal_digest(state),
        manifest_path=manifest_path,
    )
    return all(str(group.get("group_id")) in accepted for group in groups if isinstance(group, dict))


def _group_report_status(report_path: Path) -> str:
    payload = _json_load(report_path, {})
    if not isinstance(payload, dict):
        return "invalid"
    group = (
        payload.get("agent_result", {}).get("vc_proving", {}).get("group", {})
        if isinstance(payload.get("agent_result"), dict)
        else {}
    )
    if not isinstance(group, dict):
        return "invalid"
    return str(group.get("status") or "pending")


def _sync_vc_proving_next_actions(state: dict[str, Any], attempt: dict[str, Any]) -> bool:
    current_id, current_attempt = _round_attempt_for_phase(state, VC_PROVING_PREPARING_PHASE)
    if not current_id or not isinstance(current_attempt, dict) or str(current_attempt.get("round")) != str(attempt.get("round")):
        return False
    manifest_path = _manifest_path_for_attempt(attempt)
    if not manifest_path.is_file():
        return False
    manifest = _json_load(manifest_path, {})
    if not isinstance(manifest, dict):
        return False
    if _manifest_current_errors(state, attempt, manifest_path, manifest):
        return False
    groups = _manifest_groups(manifest)
    accepted_groups = _accepted_group_ids(
        state,
        round_id=str(attempt.get("round")),
        source_goal_version=_current_source_goal_digest(state),
        manifest_path=manifest_path,
    )
    parallelism_payload = attempt.get("parallelism") if isinstance(attempt.get("parallelism"), dict) else {}
    parallelism = parallelism_payload.get("max_parallel_group_workers")
    limit = int(parallelism or DEFAULT_MAX_PARALLEL_GROUP_WORKERS)
    group_report_paths: dict[str, Path] = {}
    for group in groups:
        if not isinstance(group, dict):
            continue
        handoff_files = group.get("handoff_files") if isinstance(group.get("handoff_files"), dict) else {}
        group_report_paths[str(group.get("group_id"))] = Path(str(handoff_files.get("report", "")))
    retained_actions: list[dict[str, Any]] = []
    existing_actions: list[dict[str, Any]] = []
    changed = False
    for action in state.get("next_actions", []):
        if not isinstance(action, dict) or action.get("kind") != "spawn-group-worker" or action.get("round") != attempt.get("round"):
            retained_actions.append(action)
            continue
        group_id = str(action.get("group_id"))
        report_path = group_report_paths.get(group_id)
        group = next((item for item in groups if str(item.get("group_id")) == group_id), None)
        if (
            group_id in accepted_groups
            or report_path is None
            or group is None
            or _group_entry_path_errors(state, attempt, group, require_report_pending=True)
        ):
            changed = True
            continue
        retained_actions.append(action)
        existing_actions.append(action)
    state["next_actions"] = retained_actions
    existing_ids = {str(action.get("id")) for action in existing_actions}
    ready_groups: list[dict[str, Any]] = []
    order_hint = [str(item) for item in manifest.get("dependency_ready_order", [])] if isinstance(manifest.get("dependency_ready_order"), list) else []
    order_index = {group_id: index for index, group_id in enumerate(order_hint)}
    for group in groups:
        if not isinstance(group, dict):
            continue
        group_id = str(group.get("group_id"))
        if group_id in accepted_groups:
            continue
        path_errors = _group_entry_path_errors(state, attempt, group, require_report_pending=True)
        if path_errors:
            continue
        handoff_files = group.get("handoff_files") if isinstance(group.get("handoff_files"), dict) else {}
        input_path = Path(str(handoff_files.get("input", "")))
        report_path = Path(str(handoff_files.get("report", "")))
        startup = group.get("startup") if isinstance(group.get("startup"), dict) else {}
        if startup.get("owner") != "main-agent" or startup.get("script_launch_allowed") != "no":
            continue
        if not input_path.is_file() or not report_path.is_file():
            continue
        dependencies = [str(item) for item in group.get("dependencies", [])]
        if any(dep not in accepted_groups for dep in dependencies):
            continue
        if _group_report_status(report_path) != "pending":
            continue
        ready_groups.append(group)
    ready_groups.sort(
        key=lambda group: (
            order_index.get(str(group.get("group_id")), len(order_index)),
            -float(group.get("estimated_difficulty_score", 0.0) or 0.0),
        )
    )
    available = max(0, limit - len(existing_actions))
    for group in ready_groups[:available]:
        action = _group_action_for_manifest_entry(str(attempt["round"]), group)
        if action["id"] in existing_ids:
            continue
        changed = _ensure_next_action(state, action) or changed
    return changed


def _action_validity_errors(state: dict[str, Any], action: dict[str, Any]) -> list[str]:
    if not isinstance(action, dict):
        return ["next action is not a JSON object"]
    kind = action.get("kind")
    phase = str(state.get("phase") or "")
    if kind == "spawn-attempt":
        attempt_id = str(action.get("attempt_id") or "")
        attempt = state.get("attempts", {}).get(attempt_id)
        if not isinstance(attempt, dict):
            return ["spawn-attempt target attempt is missing"]
        errors: list[str] = []
        if str(attempt.get("phase")) in VC_PROVING_PHASE_ALIASES:
            errors.append("vc-proving-preparing uses controller-owned preparing, not spawn-attempt")
        if str(action.get("phase")) != phase:
            errors.append("spawn-attempt phase does not match current controller phase")
        if not _current_attempt_matches(state, attempt_id, attempt):
            errors.append("spawn-attempt is not the latest current attempt for its phase")
        if attempt.get("status") != "pending":
            errors.append("spawn-attempt target is not pending")
        if not _same_path(action.get("input"), attempt.get("input")) or not _same_path(action.get("report"), attempt.get("report")):
            errors.append("spawn-attempt handoff paths do not match attempt record")
        if not _attempt_paths_valid(state, attempt):
            errors.append("spawn-attempt paths are outside current run/report roots")
        return errors
    if kind == "main-owned-action":
        action_name = str(action.get("action") or "")
        if action_name == "final-candidate-apply":
            accepted = state.get("accepted_rounds", {}).get(VC_PROVING_PREPARING_PHASE)
            if not isinstance(accepted, dict):
                accepted = state.get("accepted_rounds", {}).get(VC_PROVING_LEGACY_PHASE)
            final_candidate = state.get("final_candidate") if isinstance(state.get("final_candidate"), dict) else {}
            if phase != "final-check":
                return ["final-candidate-apply is only valid in final-check phase"]
            if not isinstance(accepted, dict) or accepted.get("round") != action.get("round"):
                return ["final-candidate-apply round is not the accepted vc-proving-preparing round"]
            if final_candidate.get("round") != action.get("round"):
                return ["final-candidate-apply round does not match final_candidate"]
            return []
        attempt_id = str(action.get("attempt_id") or "")
        attempt = state.get("attempts", {}).get(attempt_id)
        if not isinstance(attempt, dict):
            return ["main-owned action target attempt is missing"]
        errors = []
        if str(action.get("phase")) != phase:
            errors.append("main-owned action phase does not match current controller phase")
        if not _current_attempt_matches(state, attempt_id, attempt):
            errors.append("main-owned action is not for the latest current attempt")
        if action_name in {"annotation-check-round", "vc-checking-check-round"} and attempt.get("status") != "ready-for-main-check":
            errors.append("main-owned check action target is not ready-for-main-check")
        if action_name in {"vc-proving-preparing", "vc-proving-setup"} and attempt.get("status") != "pending":
            errors.append("vc-proving-preparing action target is not pending")
        if action_name == "vc-proving-verify" and not _all_manifest_groups_accepted(state, attempt):
            errors.append("vc-proving-verify action does not have all current manifest groups accepted")
        if not _attempt_paths_valid(state, attempt):
            errors.append("main-owned action attempt paths are outside current run/report roots")
        return errors
    if kind == "spawn-group-worker":
        if phase not in VC_PROVING_PHASE_ALIASES:
            return ["spawn-group-worker is only valid in vc-proving-preparing phase"]
        attempt_id, attempt = _round_attempt_for_phase(state, VC_PROVING_PREPARING_PHASE)
        if not attempt_id or not isinstance(attempt, dict):
            return ["no current vc-proving-preparing attempt for group action"]
        if str(action.get("round")) != str(attempt.get("round")):
            return ["group action round is not the current vc-proving round"]
        manifest_path = _manifest_path_for_attempt(attempt)
        if not manifest_path.is_file():
            return ["current vc-proving-preparing manifest is missing"]
        manifest = _json_load(manifest_path, {})
        if not isinstance(manifest, dict):
            return ["current vc-proving-preparing manifest is invalid"]
        errors = _manifest_current_errors(state, attempt, manifest_path, manifest)
        if errors:
            return errors
        group_id = str(action.get("group_id") or "")
        group = next((item for item in _manifest_groups(manifest) if str(item.get("group_id")) == group_id), None)
        if group is None:
            return ["group action group_id is not in current manifest"]
        handoff_files = group.get("handoff_files") if isinstance(group.get("handoff_files"), dict) else {}
        if not _same_path(action.get("input"), handoff_files.get("input")) or not _same_path(action.get("report"), handoff_files.get("report")):
            return ["group action handoff paths do not match current manifest"]
        errors = _group_entry_path_errors(state, attempt, group, require_report_pending=True)
        accepted_groups = _accepted_group_ids(
            state,
            round_id=str(attempt.get("round")),
            source_goal_version=_current_source_goal_digest(state),
            manifest_path=manifest_path,
        )
        if group_id in accepted_groups:
            errors.append("group is already accepted for current manifest")
        dependencies = [str(item) for item in group.get("dependencies", [])]
        missing_deps = [dep for dep in dependencies if dep not in accepted_groups]
        if missing_deps:
            errors.append("group dependencies are not accepted: " + ", ".join(missing_deps))
        return errors
    return [f"unsupported next action kind: {kind!r}"]


def _prune_stale_next_actions(state: dict[str, Any], *, reason: str) -> bool:
    actions = state.get("next_actions", [])
    if not isinstance(actions, list):
        state["next_actions"] = []
        return True
    retained: list[dict[str, Any]] = []
    removed: list[dict[str, Any]] = []
    for action in actions:
        errors = _action_validity_errors(state, action) if isinstance(action, dict) else ["next action is not a JSON object"]
        if errors:
            removed.append({"action": action, "errors": errors})
            continue
        retained.append(action)
    if not removed:
        return False
    state["next_actions"] = retained
    state.setdefault("stale_actions", []).append(
        {
            "staled_at": _utc(),
            "reason": reason,
            "removed": removed,
        }
    )
    return True


def _mark_downstream_attempts_stale(state: dict[str, Any], *, from_phase: str, reason: str) -> dict[str, Any]:
    downstream_by_phase = {
        "annotation": ["vc-checking", VC_PROVING_PREPARING_PHASE, VC_PROVING_LEGACY_PHASE],
        "vc-checking": [VC_PROVING_PREPARING_PHASE, VC_PROVING_LEGACY_PHASE],
    }
    downstream = set(downstream_by_phase.get(from_phase, []))
    staled: dict[str, Any] = {"attempts": {}, "group_attempts": {}}
    for attempt_id, attempt in state.get("attempts", {}).items():
        if not isinstance(attempt, dict) or str(attempt.get("phase")) not in downstream:
            continue
        previous = attempt.get("status")
        if previous == "stale":
            continue
        attempt["status"] = "stale"
        attempt["stale_reason"] = reason
        attempt["staled_at"] = _utc()
        staled["attempts"][attempt_id] = {
            "phase": attempt.get("phase"),
            "round": attempt.get("round"),
            "previous_status": previous,
        }
    if downstream.intersection(VC_PROVING_PHASE_ALIASES):
        for group_key, attempt in state.get("group_attempts", {}).items():
            if not isinstance(attempt, dict):
                continue
            previous = attempt.get("status")
            if previous == "stale":
                continue
            attempt["status"] = "stale"
            attempt["stale_reason"] = reason
            attempt["staled_at"] = _utc()
            staled["group_attempts"][str(group_key)] = {
                "round": attempt.get("round"),
                "group_id": attempt.get("group_id"),
                "previous_status": previous,
            }
    return {key: value for key, value in staled.items() if value}


def _round_attempt_return_errors(state: dict[str, Any], attempt_id: str, attempt: dict[str, Any], result_status: str) -> list[str]:
    if result_status == "stale":
        return []
    errors: list[str] = []
    if attempt.get("status") == "stale":
        errors.append("attempt is already stale")
    if not _current_attempt_matches(state, attempt_id, attempt):
        errors.append("attempt is not the latest current attempt for its phase")
    if not _attempt_paths_valid(state, attempt):
        errors.append("attempt paths are outside current run/report roots")
    return errors


def _group_attempt_return_errors(state: dict[str, Any], attempt: dict[str, Any], result_status: str) -> list[str]:
    if result_status == "stale":
        return []
    if attempt.get("status") == "stale":
        return ["group attempt is already stale"]
    report_path = _resolved_path(attempt.get("report"))
    if report_path is None:
        return ["group attempt report path is missing"]
    group, current_attempt, _manifest_path, errors = _group_manifest_entry_for_report(state, report_path)
    if errors:
        return errors
    if not isinstance(group, dict) or not isinstance(current_attempt, dict):
        return ["group attempt is not in current vc-proving manifest"]
    if str(group.get("group_id")) != str(attempt.get("group_id")):
        return ["group attempt group_id does not match current manifest"]
    if str(current_attempt.get("round")) != str(attempt.get("round")):
        return ["group attempt round is not the current vc-proving round"]
    return []


def _round_report_review_errors(
    state: dict[str, Any],
    attempt_id: str,
    attempt: dict[str, Any],
    report_path: Path,
) -> list[str]:
    if not isinstance(attempt, dict) or not attempt:
        return ["round report is not tracked by the current run"]
    errors: list[str] = []
    if str(state.get("phase") or "") != str(attempt.get("phase") or ""):
        errors.append("round report phase is not the current controller phase")
    if attempt.get("status") in {"stale", "accepted"}:
        errors.append(f"round attempt status is not reviewable: {attempt.get('status')}")
    if not _current_attempt_matches(state, attempt_id, attempt):
        errors.append("round report is not for the latest current attempt")
    if not _same_path(str(report_path), attempt.get("report")):
        errors.append("round report path does not match attempt record")
    if not _attempt_paths_valid(state, attempt):
        errors.append("round report paths are outside current run/report roots")
    return errors


def _round_acceptance_payload(
    phase: str,
    round_id: str,
    attempt: dict[str, Any],
    *,
    source_version: dict[str, Any],
    source_goal_version: dict[str, Any] | None,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    payload = {
        "round": round_id,
        "worktree": attempt.get("worktree"),
        "report_directory": attempt.get("report_directory"),
        "accepted_at": _utc(),
        "source_version_digest": source_version.get("digest"),
    }
    if source_goal_version is not None:
        payload["source_goal_version_digest"] = source_goal_version.get("digest")
    if extra:
        payload.update(extra)
    return payload


def _stale_downstream_acceptance(state: dict[str, Any], *, from_phase: str, reason: str) -> dict[str, Any]:
    downstream_by_phase = {
        "annotation": ["vc-checking", VC_PROVING_PREPARING_PHASE, VC_PROVING_LEGACY_PHASE],
        "vc-checking": [VC_PROVING_PREPARING_PHASE, VC_PROVING_LEGACY_PHASE],
    }
    stale: dict[str, Any] = {}
    accepted_rounds = state.setdefault("accepted_rounds", {})
    if not isinstance(accepted_rounds, dict):
        state["accepted_rounds"] = accepted_rounds = {}
    for phase in downstream_by_phase.get(from_phase, []):
        payload = accepted_rounds.pop(phase, None)
        if payload is not None:
            stale[phase] = payload
    staled_attempts = _mark_downstream_attempts_stale(state, from_phase=from_phase, reason=reason)
    if staled_attempts:
        stale["attempt_state"] = staled_attempts
    if from_phase in {"annotation", "vc-checking"}:
        group_acceptance = state.get("group_acceptance")
        if group_acceptance:
            stale["group_acceptance"] = group_acceptance
        state["group_acceptance"] = {}
    if _prune_stale_next_actions(state, reason=reason):
        stale["next_actions"] = "pruned"
    if stale:
        state.setdefault("stale_graph", {})[_utc()] = {
            "from_phase": from_phase,
            "reason": reason,
            "staled": stale,
        }
    return stale


def _default_reference_policy(mode: str, target_rel: str | None = None) -> dict[str, Any]:
    if mode == "deny-existing-examples":
        allowed = [
            ".agents/**",
            ".agents/skills/**",
            "QCP_examples/QCP_demos_LLM/**",
            "QCP_examples/LLM_bench/**",
            "SeparationLogic/examples/LLM_bench/**",
            "QCP_examples/QCP_demos_LLM/verification_stdlib.h",
            "QCP_examples/QCP_demos_LLM/verification_list.h",
            "QCP_examples/QCP_demos_LLM/int_array_def.h",
        ]
        if target_rel:
            allowed.insert(0, target_rel)
            target_files = _target_files_for_rel(target_rel)
            allowed.extend(
                [
                    target_files["goal_file"],
                    target_files["proof_auto_file"],
                    target_files["proof_manual_file"],
                    target_files["goal_check_file"],
                    target_files["proof_diagnostics_file"],
                    target_files["diagnostics_snapshot"],
                ]
            )
        return {
            "mode": mode,
            "allowed_globs": allowed,
            "denied_globs": [
                "QCP_examples/QCP_demos_human/**",
                "SeparationLogic/examples/QCP_demos_human/**",
            ],
            "must_log_file_reads": "yes",
        }
    return {
        "mode": "default",
        "allowed_globs": [],
        "denied_globs": [
            "QCP_examples/QCP_demos_human/**",
            "SeparationLogic/examples/QCP_demos_human/**",
        ],
        "must_log_file_reads": "yes",
    }


def _annotation_contract() -> dict[str, Any]:
    return {
        "subagent_skills": ["annotation-filling", "annotation-checking"],
        "no_existing_lib_policy": "create-minimal-case-lib-then-bootstrap-spec",
        "self_repair_budget": dict(DEFAULT_SELF_REPAIR_BUDGET),
        "self_reworkable_failure_classes": list(SELF_REWORKABLE_FAILURE_CLASSES),
        "ready_condition": (
            "agent_result.annotation.status == completed and "
            "ready_for_annotation_check_round == true only after canonical QCP, "
            "case_lib coqc, and annotation-checking pass; "
            "self_reworkable_failures must be empty"
        ),
        "blocked_condition": (
            "only phase skill hard blockers should use status == blocked; "
            "self_repair_budget_exhausted is work evidence, not an automatic blocked condition"
        ),
    }


def _run_root_from_id(main_root: Path, run_id: str) -> Path:
    run_root = main_root / "worktrees" / run_id
    if not run_root.is_dir():
        raise SystemExit(f"run root not found: {run_root}")
    return run_root.resolve()


def load_latest_state_snapshot(run_root: Path) -> dict[str, Any] | None:
    path = run_logs_path(run_root)
    if not path.is_file():
        return None
    latest: dict[str, Any] | None = None
    for line_number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not raw_line.strip():
            continue
        try:
            record = json.loads(raw_line)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"invalid run_logs.json record at line {line_number}: {exc}") from exc
        if not isinstance(record, dict):
            raise SystemExit(f"invalid run_logs.json record at line {line_number}: expected object")
        if record.get("record_kind") != "state_snapshot":
            continue
        state = record.get("state")
        if isinstance(state, dict):
            latest = state
    return latest


def append_run_log_record(run_root: Path, record: dict[str, Any]) -> None:
    path = run_logs_path(run_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=True, sort_keys=True) + "\n")


def _load_state(run_root: Path) -> dict[str, Any]:
    state = load_latest_state_snapshot(run_root)
    if isinstance(state, dict):
        return state
    path = run_status_path(run_root)
    state = _json_load(path)
    if not isinstance(state, dict):
        raise SystemExit(f"run_logs.json state snapshot or legacy run_status.json missing or invalid: {run_root}")
    return state


def _save_state(run_root: Path, state: dict[str, Any]) -> None:
    state["updated_at"] = _utc()
    append_run_log_record(
        run_root,
        {
            "schema_version": SCHEMA_RUN_LOG,
            "record_kind": "state_snapshot",
            "timestamp": _utc(),
            "run_id": state.get("run_id", run_root.name),
            "phase": state.get("phase"),
            "state": state,
        },
    )


def _event_id(run_root: Path, event: str, attempt: str | None = None) -> str:
    events_path = run_logs_path(run_root)
    count = 0
    if events_path.is_file():
        count = sum(1 for line in events_path.read_text(encoding="utf-8").splitlines() if line.strip())
    raw = f"{run_root.name}:{count + 1}:{event}:{attempt or ''}:{_utc()}"
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:20]


def _append_event(
    run_root: Path,
    state: dict[str, Any],
    event: str,
    *,
    phase: str | None = None,
    round_id: str | None = None,
    group_id: str | None = None,
    attempt_id: str | None = None,
    details: dict[str, Any] | None = None,
) -> None:
    payload = {
        "schema_version": SCHEMA_RUN_LOG,
        "record_kind": "event",
        "event_id": _event_id(run_root, event, attempt_id),
        "timestamp": _utc(),
        "run_id": state.get("run_id", run_root.name),
        "actor": "controller",
        "event": event,
        "phase": phase or state.get("phase"),
        "round": round_id,
        "group": group_id,
        "attempt": attempt_id,
        "source_version": state.get("source_version"),
        "source_goal_version": state.get("source_goal_version"),
        "details": details or {},
    }
    append_run_log_record(run_root, payload)


def _timing_template(report_root: Path) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_TIMING_SUMMARY,
        "run_id": report_root.name,
        "time_format": "UTC ISO-8601",
        "nodes": [],
        "duration_summary": {
            "closed_interval_count": 0,
            "categories": {},
        },
        "phase_time": {},
        "worker_time": {},
        "coq_time": {},
        "retry_reasons": {},
        "compact_counts": {},
        "stale_lost_time": {},
    }


def _parse_timing_timestamp(value: Any) -> datetime | None:
    if not isinstance(value, str) or not value.strip():
        return None
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def _timing_duration_seconds(start: Any, end: Any) -> float | None:
    start_dt = _parse_timing_timestamp(start)
    end_dt = _parse_timing_timestamp(end)
    if start_dt is None or end_dt is None:
        return None
    return round(max(0.0, (end_dt - start_dt).total_seconds()), 6)


def _timing_bucket(categories: dict[str, Any], category: str, name: str) -> dict[str, Any]:
    category_payload = categories.setdefault(category, {})
    bucket = category_payload.setdefault(
        name,
        {
            "count": 0,
            "total_seconds": 0.0,
            "first_started_at": None,
            "last_ended_at": None,
            "last_duration_seconds": None,
        },
    )
    return bucket


def _recompute_timing_durations(summary: dict[str, Any]) -> None:
    nodes = summary.get("nodes")
    if not isinstance(nodes, list):
        nodes = []
        summary["nodes"] = nodes
    open_nodes: dict[str, list[dict[str, Any]]] = {}
    categories: dict[str, Any] = {}
    closed_count = 0
    for index, node in enumerate(nodes, start=1):
        if not isinstance(node, dict):
            continue
        node["sequence"] = index
        node_type = str(node.get("node_type") or "")
        timer_key = str(node.get("timer_key") or "")
        if not timer_key:
            timer_key = f"{node.get('category') or 'event'}:{node.get('name') or node.get('event') or index}"
            node["timer_key"] = timer_key
        if node_type == "start":
            node.pop("duration_seconds", None)
            node.pop("paired_start_sequence", None)
            open_nodes.setdefault(timer_key, []).append(node)
            continue
        if node_type != "end":
            node.pop("duration_seconds", None)
            node.pop("paired_start_sequence", None)
            continue
        starts = open_nodes.get(timer_key) or []
        if not starts:
            node.pop("duration_seconds", None)
            node.pop("paired_start_sequence", None)
            continue
        start_node = starts.pop()
        duration = _timing_duration_seconds(start_node.get("timestamp"), node.get("timestamp"))
        if duration is None:
            node.pop("duration_seconds", None)
            node.pop("paired_start_sequence", None)
            continue
        node["duration_seconds"] = duration
        node["paired_start_sequence"] = start_node.get("sequence")
        closed_count += 1
        category = str(node.get("category") or start_node.get("category") or "event")
        name = str(node.get("name") or start_node.get("name") or timer_key)
        bucket = _timing_bucket(categories, category, name)
        bucket["count"] += 1
        bucket["total_seconds"] = round(float(bucket["total_seconds"]) + duration, 6)
        bucket["last_duration_seconds"] = duration
        if bucket["first_started_at"] is None:
            bucket["first_started_at"] = start_node.get("timestamp")
        bucket["last_ended_at"] = node.get("timestamp")
    summary["duration_summary"] = {
        "closed_interval_count": closed_count,
        "categories": categories,
    }
    summary["phase_time"] = categories.get("phase", {})
    worker_time: dict[str, Any] = {}
    worker_time.update(categories.get("attempt", {}))
    worker_time.update(categories.get("group_worker", {}))
    summary["worker_time"] = worker_time


def _load_timing_summary(report_root: Path) -> dict[str, Any]:
    path = report_root / "timing_summary.json"
    payload = _json_load(path, {})
    if not isinstance(payload, dict):
        payload = {}
    template = _timing_template(report_root)
    if payload.get("schema_version") != SCHEMA_TIMING_SUMMARY:
        migrated = template
        for legacy_key in ("phase_time", "worker_time", "coq_time", "retry_reasons", "compact_counts", "stale_lost_time"):
            if isinstance(payload.get(legacy_key), dict):
                migrated[legacy_key] = payload[legacy_key]
        if isinstance(payload.get("nodes"), list):
            migrated["nodes"] = payload["nodes"]
        payload = migrated
    else:
        for key, value in template.items():
            payload.setdefault(key, value)
    if not isinstance(payload.get("nodes"), list):
        payload["nodes"] = []
    _recompute_timing_durations(payload)
    return payload


def _write_timing_summary(report_root: Path) -> None:
    write_json(report_root / "timing_summary.json", _load_timing_summary(report_root))


def _append_timing_node(
    report_root: Path,
    *,
    event: str,
    node_type: str,
    category: str,
    name: str,
    timestamp: str | None = None,
    phase: str | None = None,
    round_id: str | None = None,
    group_id: str | None = None,
    attempt_id: str | None = None,
    timer_key: str | None = None,
) -> None:
    payload = _load_timing_summary(report_root)
    nodes = payload.setdefault("nodes", [])
    if not isinstance(nodes, list):
        nodes = []
        payload["nodes"] = nodes
    node = {
        "sequence": len(nodes) + 1,
        "event": event,
        "node_type": node_type,
        "timestamp": timestamp or _utc_timing(),
        "category": category,
        "name": name,
        "phase": phase,
        "round": round_id,
        "group": group_id,
        "attempt": attempt_id,
        "timer_key": timer_key or f"{category}:{name}",
    }
    nodes.append(node)
    _recompute_timing_durations(payload)
    write_json(report_root / "timing_summary.json", payload)


def _report_root_from_state(run_root: Path, state: dict[str, Any] | None = None) -> Path:
    if isinstance(state, dict) and state.get("report_root"):
        return Path(str(state["report_root"])).expanduser().resolve()
    return reports_root(run_root)


def _append_run_timing_node(
    run_root: Path,
    state: dict[str, Any] | None,
    *,
    event: str,
    node_type: str,
    category: str,
    name: str,
    timestamp: str | None = None,
    phase: str | None = None,
    round_id: str | None = None,
    group_id: str | None = None,
    attempt_id: str | None = None,
    timer_key: str | None = None,
) -> None:
    _append_timing_node(
        _report_root_from_state(run_root, state),
        event=event,
        node_type=node_type,
        category=category,
        name=name,
        timestamp=timestamp,
        phase=phase if phase is not None else (state.get("phase") if isinstance(state, dict) else None),
        round_id=round_id,
        group_id=group_id,
        attempt_id=attempt_id,
        timer_key=timer_key,
    )


def _append_phase_transition_timing(
    run_root: Path,
    state: dict[str, Any],
    *,
    previous_phase: str | None,
    next_phase: str | None,
    timestamp: str | None = None,
) -> None:
    if not previous_phase or not next_phase or previous_phase == next_phase:
        return
    when = timestamp or _utc_timing()
    _append_run_timing_node(
        run_root,
        state,
        event="phase-end",
        node_type="end",
        category="phase",
        name=previous_phase,
        timestamp=when,
        phase=previous_phase,
        timer_key=f"phase:{previous_phase}",
    )
    if next_phase != "done":
        _append_run_timing_node(
            run_root,
            state,
            event="phase-start",
            node_type="start",
            category="phase",
            name=next_phase,
            timestamp=when,
            phase=next_phase,
            timer_key=f"phase:{next_phase}",
        )
    else:
        _append_run_timing_node(
            run_root,
            state,
            event="run-end",
            node_type="end",
            category="run",
            name=str(state.get("run_id", run_root.name)),
            timestamp=when,
            phase=next_phase,
            timer_key=f"run:{state.get('run_id', run_root.name)}",
        )


def _git_worktree_add(source: Path, target: Path) -> None:
    if target.exists():
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    proc = subprocess.run(
        ["git", "worktree", "add", "--detach", str(target), "HEAD"],
        cwd=source,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise SystemExit(proc.stderr.strip() or proc.stdout.strip())
    status_proc = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=source,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if status_proc.returncode != 0:
        raise SystemExit(status_proc.stderr.strip() or status_proc.stdout.strip())
    for raw_line in status_proc.stdout.splitlines():
        line = raw_line.rstrip()
        if len(line) < 4:
            continue
        code = line[:2]
        rel_text = line[3:]
        if " -> " in rel_text:
            _old, rel_text = rel_text.split(" -> ", 1)
        rel_path = Path(rel_text)
        src_path = source / rel_path
        dest_path = target / rel_path
        if "D" in code and not src_path.exists():
            if dest_path.exists():
                if dest_path.is_dir():
                    shutil.rmtree(dest_path)
                else:
                    dest_path.unlink()
            continue
        if src_path.is_file():
            dest_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src_path, dest_path)


def _spawn_message(input_path: Path, report_path: Path) -> str:
    return "\n".join(
        [
            f"Read {input_path}.",
            f"The goal is to complete the workflow task assigned by the input JSON; {report_path} is only the final report file recording the result.",
            "Before acting, read the input JSON completely and read every skill or rule file listed in handoff.rules_source.",
            "The input JSON, declared round worktree, declared source versions, and current files are the source of truth.",
            "Do not rely on parent chat history or unstated assumptions as task context or evidence.",
            "Minimize respawns: perform repair, retry, missing-file bootstrap, and alternative attempts inside this same spawn whenever the input versions are still current.",
            "Do not stop for confirmation about optional context, missing bootstrap files, future proof difficulty, or recoverable tool feedback; make a conservative local choice and continue.",
            "Work only in the declared round worktree; write only the declared report/output files and formal files allowed by allowed_write_paths.",
            "No compromise operations: do not weaken specifications, bypass required checks, fake evidence, change generated files by hand, change witness statements to fit a proof, add Admitted/Axiom, use forbidden tools/tactics, or edit paths outside the handoff.",
            "Task completion means the assigned phase work is completed under the strict workflow, with a terminal agent_result, required evidence, changed-files or blocker details, applicable source_version/source_goal_version, and an output note satisfying output_contract.",
            "Controller acceptance is separate; do not mark yourself accepted or claim acceptance unless the controller writes it.",
            "Reuse only previous_attempts, required_lessons, prior_failure_summaries, and output notes declared in the JSON; previous outputs are non-authoritative and lose conflicts to JSON, manifests, source versions, and current files.",
            "Compact-error is not your blocked judgment; report it only as a compaction fact and let controller/main decide retry or final blocker.",
            "If the strict workflow cannot be completed, write a blocked, stale, or compact-error result with concrete evidence instead of improvising around the process.",
        ]
    )


def _round_attempt_paths(report_root: Path, round_id: str) -> dict[str, Path]:
    directory = report_root / "rounds" / round_id
    return {
        "directory": directory,
        "input": directory / "agent_input.json",
        "report": directory / "agent_report.json",
        "output": directory / "agent_output.txt",
    }


def _attempt_control_payload(round_id: str, attempt_index: int, max_compact_attempts: int) -> dict[str, Any]:
    return {
        "attempt_id": f"{round_id}-attempt-{attempt_index}",
        "attempt_index": attempt_index,
        "max_compact_attempts": max_compact_attempts,
        "retry_reasons": sorted(RETRY_REASONS),
        "heartbeat_policy": "no-timeout-retry",
    }


def _output_contract_payload(output_path: Path) -> dict[str, Any]:
    return {
        "path": str(output_path),
        "kind": "non-authoritative-reuse-note",
        "required": "yes",
        "acceptance_evidence": "no",
        "must_start_with": "# Reuse Note",
        "must_contain": ["Note kind: non-authoritative reuse note"],
        "conflict_rule": "json_handoff_manifest_versions_and_current_files_win",
    }


def build_agent_input_payload(
    *,
    state: dict[str, Any],
    run_root: Path,
    phase: str,
    round_id: str,
    attempt_index: int,
    worktree_path: Path,
    source_worktree: Path,
    paths: dict[str, Path],
    source_version: dict[str, Any] | None,
    previous_attempts: list[dict[str, Any]] | None = None,
    required_lessons: list[dict[str, Any]] | None = None,
    prior_failure_summaries: list[dict[str, Any]] | None = None,
    case_lib_seed_evidence: dict[str, Any] | None = None,
) -> dict[str, Any]:
    target_files = _target_files_for_state(state)
    rules_source = _rules_source_for_phase(phase)
    problem_context = _normalized_problem_context(state)
    attempt_control = _attempt_control_payload(
        round_id,
        attempt_index,
        int(state.get("max_compact_attempts", 3)),
    )
    payload: dict[str, Any] = {
        "schema_version": "qcp-agent-input/v1",
        "phase": phase,
        "round": round_id,
        "attempt_control": attempt_control,
        "run": {
            "run_id": state["run_id"],
            "run_root": str(run_root),
            "report_root": state["report_root"],
            "main_worktree": state["main_worktree"],
        },
        "round_worktree": str(worktree_path),
        "parent_worktree": str(source_worktree.resolve()),
        "startup": {
            "owner": "main-agent",
            "controller_owned_state": "yes",
            "script_launch_allowed": "no",
        },
        "single_spawn_policy": {
            "preferred": "yes",
            "goal": "complete all feasible phase repair and validation attempts inside this one spawn",
            "continue_without_confirmation": [
                "missing optional problem context",
                "missing case_lib seed when phase policy permits bootstrap",
                "missing generated diagnostic hint files",
                "spec uncertainty resolvable from C code and problem_context",
                "future proof difficulty",
                "recoverable QCP or Coq feedback",
            ],
            "create_missing_allowed_files": "yes",
            "retry_inside_spawn": "yes",
            "terminal_blocked_only_for": [
                "phase skill declares the current task semantically impossible under current inputs",
                "required toolchain completely unavailable after command evidence",
            ],
            "state_reports": {
                "stale": "report stale when source_version or source_goal_version is no longer current",
                "compact_error": "report compact-error only as a compaction fact; controller/main decides retry or final blocker",
            },
            "controller_acceptance_model": "controller validates final candidate and evidence after spawn returns",
        },
        "handoff": {
            "rendered_instructions_compact": _spawn_message(paths["input"], paths["report"]),
            "rules_source": rules_source,
        },
        "source_version": source_version,
        "source_goal_version": state.get("source_goal_version"),
        "problem_context": problem_context,
        "target_files": {
            key: value
            for key, value in target_files.items()
            if key not in {"case_name", "active_case_theory"}
        },
        "case_lib": target_files["case_lib"],
        "allowed_write_paths": _allowed_write_paths(phase, target_files),
        "coq_tooling": _coq_tooling_payload(phase, state, worktree_path, target_files),
        "compact_retry": {
            "attempt_index": attempt_index,
            "max_compact_attempts": state.get("max_compact_attempts", 3),
        },
        "reports": {key: str(path) for key, path in paths.items() if key != "directory"},
        "output_contract": _output_contract_payload(paths["output"]),
    }
    if phase == "annotation":
        payload["annotation_contract"] = _annotation_contract()
        payload["case_lib_seed_evidence"] = case_lib_seed_evidence or {"status": "not-applicable"}
        payload["reference_policy"] = state.get("reference_policy") or _default_reference_policy("default")
        payload["previous_attempts"] = previous_attempts or []
        payload["required_lessons"] = required_lessons or []
        payload["prior_failure_summaries"] = prior_failure_summaries or []
        payload["qcp_driver"] = _qcp_driver_payload(state, worktree_path, target_files)
        payload["spec_requirements"] = {
            **_annotation_spec_requirements(str(target_files["case_name"])),
            "problem_context_summary": {
                "target_function": problem_context["target_function"],
                "expected_behavior": problem_context["expected_behavior"],
                "input_output_contract": problem_context["input_output_contract"],
                "spec_hint": problem_context["spec_hint"],
                "preferred_hidden_properties": problem_context["preferred_hidden_properties"],
                "source": problem_context["source"],
            },
            "bootstrap_required_when_case_lib_seed_created": "yes",
        }
    if phase == "vc-checking":
        payload["spawn"] = {
            "fork_context": False,
            "fork_turns": "none",
            "parent_context_allowed": False,
        }
        payload["context_policy"] = {
            "source_of_truth": "agent_input_json_and_round_worktree",
            "main_agent_transcript_allowed": "no",
        }
        accepted_annotation = state.get("accepted_rounds", {}).get("annotation")
        payload["accepted_annotation_report"] = (
            str(Path(str(accepted_annotation["report_directory"])) / "agent_report.json")
            if isinstance(accepted_annotation, dict) and accepted_annotation.get("report_directory")
            else None
        )
        payload["annotation_design_summary"] = state.get("annotation_design_summary") or {}
        payload["diagnostics"] = {
            "proof_diagnostics_file": target_files["proof_diagnostics_file"],
            "diagnostics_snapshot": target_files["diagnostics_snapshot"],
            "hint_only": "yes",
        }
        payload["grouping_policy"] = {
            "controller_policy": "bounded-witness-groups/v1",
            "balanced_grouping_required": "yes",
            "max_witnesses_per_group": DEFAULT_MAX_WITNESSES_PER_GROUP,
            "single_group_allowed_only_if_target_witness_count_lte": DEFAULT_MAX_WITNESSES_PER_GROUP,
            "oversized_group_rejected_by_controller": "yes",
            "grouping_basis": [
                "same proof pattern or helper family",
                "same loop/refinement phase",
                "dependency ordering",
                "manual witness order as deterministic tie-breaker",
            ],
            "split_required_when": [
                f"target witness count exceeds {DEFAULT_MAX_WITNESSES_PER_GROUP}",
                f"any proposed group would exceed {DEFAULT_MAX_WITNESSES_PER_GROUP} witnesses",
                "proof strategies are unrelated enough to confuse one worker",
            ],
            "same_function_related_witnesses": "keep-together-only-within-max-witnesses-per-group",
            "reason_required_for_each_group": "yes",
        }
    if phase == "vc-proving":
        payload["parallelism"] = {
            "max_parallel_group_workers": DEFAULT_MAX_PARALLEL_GROUP_WORKERS,
        }
        payload["annotation_design_summary"] = state.get("annotation_design_summary") or {}
    return payload


def build_agent_report_payload(phase: str) -> dict[str, Any]:
    return {
        "schema_version": "qcp-agent-report/v1",
        "kind": phase,
        "status": "pending",
        "terminal": "no",
        "agent_result": {},
        "verification_result": {},
        "blockers": [],
    }


def _init_round_attempt(
    *,
    run_root: Path,
    state: dict[str, Any],
    phase: str,
    round_id: str,
    source_worktree: Path,
    attempt_index: int,
    previous_attempts: list[dict[str, Any]] | None = None,
    required_lessons: list[dict[str, Any]] | None = None,
    prior_failure_summaries: list[dict[str, Any]] | None = None,
    annotation_source_annotated: bool = False,
) -> dict[str, Any]:
    report_root = Path(str(state["report_root"]))
    worktree_path = run_root / round_id
    _git_worktree_add(source_worktree, worktree_path)
    paths = _round_attempt_paths(report_root, round_id)
    paths["directory"].mkdir(parents=True, exist_ok=True)
    attempt_id = f"{round_id}-attempt-{attempt_index}"
    target_files = _target_files_for_state(state)
    case_lib_seed_evidence = (
        _ensure_case_lib_seed(worktree_path, target_files)
        if phase == "annotation"
        else None
    )
    source_version = (
        _source_version_for_workspace(state, worktree_path, annotated=annotation_source_annotated)
        if phase == "annotation"
        else state.get("source_version")
    )
    input_payload = build_agent_input_payload(
        state=state,
        run_root=run_root,
        phase=phase,
        round_id=round_id,
        attempt_index=attempt_index,
        worktree_path=worktree_path,
        source_worktree=source_worktree,
        paths=paths,
        source_version=source_version,
        previous_attempts=previous_attempts,
        required_lessons=required_lessons,
        prior_failure_summaries=prior_failure_summaries,
        case_lib_seed_evidence=case_lib_seed_evidence,
    )
    report_payload = build_agent_report_payload(phase)
    write_json(paths["input"], input_payload)
    write_json(paths["report"], report_payload)
    paths["output"].write_text("", encoding="utf-8")
    attempt = {
        "attempt_id": attempt_id,
        "phase": phase,
        "round": round_id,
        "attempt_index": attempt_index,
        "status": "pending",
        "worktree": str(worktree_path),
        "report_directory": str(paths["directory"]),
        "input": str(paths["input"]),
        "report": str(paths["report"]),
    }
    state.setdefault("attempts", {})[attempt_id] = attempt
    return attempt


def _init_vc_proving_preparing_attempt(
    *,
    run_root: Path,
    state: dict[str, Any],
    round_id: str,
    source_worktree: Path,
    attempt_index: int,
) -> dict[str, Any]:
    report_root = Path(str(state["report_root"]))
    report_dir = report_root / "rounds" / round_id
    report_dir.mkdir(parents=True, exist_ok=True)
    container_dir = run_root / round_id
    container_dir.mkdir(parents=True, exist_ok=True)
    attempt_id = f"{round_id}-attempt-{attempt_index}"
    attempt = {
        "attempt_id": attempt_id,
        "phase": VC_PROVING_PREPARING_PHASE,
        "round": round_id,
        "attempt_index": attempt_index,
        "status": "pending",
        "controller_owned": "yes",
        "worktree": str(source_worktree.resolve()),
        "source_worktree": str(source_worktree.resolve()),
        "container_directory": str(container_dir.resolve()),
        "report_directory": str(report_dir.resolve()),
        "manifest": str((report_dir / "group_workers_manifest.json").resolve()),
        "group_merged_result": str((report_dir / "group_merged_result.json").resolve()),
        "parallelism": {
            "max_parallel_group_workers": DEFAULT_MAX_PARALLEL_GROUP_WORKERS,
        },
    }
    state.setdefault("attempts", {})[attempt_id] = attempt
    return attempt


def init_run(args: argparse.Namespace) -> int:
    command_started_at = _utc_timing()
    target = Path(args.target_c_file).expanduser().resolve()
    if not target.is_file():
        raise SystemExit(f"target C file not found: {target}")
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else git_toplevel(target)
    target_rel = _relative_path_for_digest(target, main_root)
    run_root = ensure_run_root(main_root, args.case, timestamp=args.timestamp)
    report_root = reports_root(run_root)
    _write_timing_summary(report_root)
    _append_timing_node(
        report_root,
        event="controller-command-start",
        node_type="start",
        category="controller_command",
        name="init-run",
        timestamp=command_started_at,
        phase="intake",
        timer_key="controller_command:init-run",
    )
    _append_timing_node(
        report_root,
        event="run-start",
        node_type="start",
        category="run",
        name=run_root.name,
        timestamp=command_started_at,
        phase="intake",
        timer_key=f"run:{run_root.name}",
    )
    _append_timing_node(
        report_root,
        event="phase-start",
        node_type="start",
        category="phase",
        name="intake",
        timestamp=command_started_at,
        phase="intake",
        timer_key="phase:intake",
    )
    reference_policy = _default_reference_policy(args.reference_policy_mode, target_rel)
    if args.allowed_reference_glob:
        reference_policy["allowed_globs"] = list(args.allowed_reference_glob)
    if args.denied_reference_glob:
        reference_policy["denied_globs"] = list(args.denied_reference_glob)
    reference_policy["must_log_file_reads"] = args.must_log_file_reads
    problem_context = _problem_context_from_args(args)
    state = {
        "schema_version": SCHEMA_STATE,
        "run_id": run_root.name,
        "case": args.case,
        "phase": "intake",
        "main_worktree": str(main_root),
        "run_root": str(run_root),
        "report_root": str(report_root),
        "target_c_file": str(target),
        "source_version": _source_version_for_workspace(
            {
                "main_worktree": str(main_root),
                "target_c_file": str(target),
            },
            main_root,
            annotated=False,
        ),
        "source_goal_version": None,
        "problem_context": problem_context,
        "reference_policy": reference_policy,
        "accepted_rounds": {},
        "group_acceptance": {},
        "attempts": {},
        "current_blockers": [],
        "next_actions": [],
        "stale_graph": {},
        "max_compact_attempts": args.max_compact_attempts,
        "created_at": _utc(),
        "updated_at": _utc(),
    }
    _save_state(run_root, state)
    _append_event(run_root, state, "run-initialized", phase="intake", details={"target_c_file": str(target)})
    _append_timing_node(
        report_root,
        event="controller-command-end",
        node_type="end",
        category="controller_command",
        name="init-run",
        phase="intake",
        timer_key="controller_command:init-run",
    )
    print(json.dumps({"run_id": run_root.name, "run_root": str(run_root), "report_root": str(report_root)}, indent=2))
    return 0


def _ensure_next_action(state: dict[str, Any], action: dict[str, Any]) -> bool:
    actions = state.setdefault("next_actions", [])
    for existing in actions:
        if isinstance(existing, dict) and existing.get("id") == action["id"]:
            return False
    actions.append(action)
    return True


def step(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous_phase = str(state.get("phase") or "")
    changed = _prune_stale_next_actions(state, reason="controller step boundary validation")
    if state.get("phase") == "intake":
        round_id = f"{slug(state['case'])}-annotation-r1"
        attempt_id = f"{round_id}-attempt-1"
        if attempt_id not in state.get("attempts", {}):
            attempt = _init_round_attempt(
                run_root=run_root,
                state=state,
                phase="annotation",
                round_id=round_id,
                source_worktree=Path(str(state["main_worktree"])),
                attempt_index=1,
            )
            _append_event(
                run_root,
                state,
                "attempt-created",
                phase="annotation",
                round_id=round_id,
                attempt_id=attempt_id,
                details={"input": attempt["input"], "report": attempt["report"]},
            )
            changed = True
        attempt = state["attempts"][attempt_id]
        changed = _ensure_next_action(state, _spawn_action_for_attempt(attempt)) or changed
        state["phase"] = "annotation"
    elif state.get("phase") == "annotation":
        _attempt_id, attempt = _round_attempt_for_phase(state, "annotation")
        if attempt and attempt.get("status") == "ready-for-main-check":
            changed = _ensure_next_action(
                state,
                _main_owned_action("annotation-check-round", round_id=str(attempt["round"]), attempt=attempt),
            ) or changed
    elif state.get("phase") == "vc-checking":
        attempt_id, attempt = _round_attempt_for_phase(state, "vc-checking")
        if attempt is None:
            parent = state.get("accepted_rounds", {}).get("annotation")
            if isinstance(parent, dict):
                round_id = _next_round_id(state, "vc-checking")
                attempt = _init_round_attempt(
                    run_root=run_root,
                    state=state,
                    phase="vc-checking",
                    round_id=round_id,
                    source_worktree=Path(str(parent["worktree"])),
                    attempt_index=1,
                )
                attempt_id = attempt["attempt_id"]
                _append_event(
                    run_root,
                    state,
                    "attempt-created",
                    phase="vc-checking",
                    round_id=round_id,
                    attempt_id=attempt_id,
                    details={
                        "input": attempt["input"],
                        "report": attempt["report"],
                        "parent_worktree": parent["worktree"],
                    },
                )
                changed = True
        if attempt is not None:
            if attempt.get("status") == "pending":
                changed = _ensure_next_action(state, _spawn_action_for_attempt(attempt)) or changed
            elif attempt.get("status") == "ready-for-main-check":
                changed = _ensure_next_action(
                    state,
                    _main_owned_action("vc-checking-check-round", round_id=str(attempt["round"]), attempt=attempt),
                ) or changed
    elif state.get("phase") in VC_PROVING_PHASE_ALIASES:
        attempt_id, attempt = _round_attempt_for_phase(state, VC_PROVING_PREPARING_PHASE)
        if attempt is None:
            parent = state.get("accepted_rounds", {}).get("vc-checking")
            if isinstance(parent, dict):
                round_id = _next_round_id(state, VC_PROVING_PREPARING_PHASE)
                attempt = _init_vc_proving_preparing_attempt(
                    run_root=run_root,
                    state=state,
                    round_id=round_id,
                    source_worktree=Path(str(parent["worktree"])),
                    attempt_index=1,
                )
                attempt_id = attempt["attempt_id"]
                _append_event(
                    run_root,
                    state,
                    "vc-proving-preparing-created",
                    phase=VC_PROVING_PREPARING_PHASE,
                    round_id=round_id,
                    attempt_id=attempt_id,
                    details={
                        "container_directory": attempt["container_directory"],
                        "report_directory": attempt["report_directory"],
                        "parent_worktree": parent["worktree"],
                    },
                )
                changed = True
        if attempt is not None:
            if attempt.get("status") == "pending":
                changed = _ensure_next_action(
                    state,
                    _main_owned_action("vc-proving-preparing", round_id=str(attempt["round"]), attempt=attempt),
                ) or changed
            changed = _sync_vc_proving_next_actions(state, attempt) or changed
            if _all_manifest_groups_accepted(state, attempt):
                changed = _ensure_next_action(
                    state,
                    _main_owned_action("vc-proving-verify", round_id=str(attempt["round"]), attempt=attempt),
                ) or changed
    changed = _prune_stale_next_actions(state, reason="controller step post-schedule boundary validation") or changed
    if changed:
        _append_phase_transition_timing(
            run_root,
            state,
            previous_phase=previous_phase,
            next_phase=str(state.get("phase") or ""),
        )
        _save_state(run_root, state)
    print(json.dumps({"run_id": state["run_id"], "phase": state["phase"], "next_actions": state.get("next_actions", [])}, indent=2))
    return 0


def spawn_instructions(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    for action in state.get("next_actions", []):
        if isinstance(action, dict) and action.get("id") == args.next_action:
            errors = _action_validity_errors(state, action)
            if errors:
                _prune_stale_next_actions(state, reason="spawn-instructions boundary validation")
                _save_state(run_root, state)
                raise SystemExit("next action is stale: " + "; ".join(errors))
            if action.get("kind") == "main-owned-action":
                raise SystemExit(
                    "next action is main-owned; run controller command "
                    f"{action.get('action')} for round {action.get('round')} instead of spawn-instructions"
                )
            input_path = Path(str(action["input"]))
            report_path = Path(str(action["report"]))
            spawn_message = _spawn_message(input_path, report_path)
            if action.get("kind") == "spawn-group-worker":
                input_payload = _json_load(input_path, {})
                if isinstance(input_payload, dict):
                    zero_context = (
                        input_payload.get("zero_context_protocol")
                        if isinstance(input_payload.get("zero_context_protocol"), dict)
                        else {}
                    )
                    if isinstance(zero_context.get("spawn_message"), str) and zero_context["spawn_message"].strip():
                        spawn_message = zero_context["spawn_message"]
            print(
                json.dumps(
                    {
                        "schema_version": "qcp-spawn-instructions/v1",
                        "next_action": args.next_action,
                        "spawn_message": spawn_message,
                        "input": str(input_path),
                        "report": str(report_path),
                    },
                    indent=2,
                )
            )
            return 0
    raise SystemExit(f"next action not found: {args.next_action}")


def _find_attempt(state: dict[str, Any], identifier: str) -> tuple[str, dict[str, Any]]:
    for attempt_id, attempt in state.get("attempts", {}).items():
        if not isinstance(attempt, dict):
            continue
        candidates = {
            attempt_id,
            str(attempt.get("round")),
            str(attempt.get("report_directory")),
            str(attempt.get("input")),
            str(attempt.get("report")),
        }
        if identifier in candidates:
            return attempt_id, attempt
    raise SystemExit(f"attempt not found: {identifier}")


def _find_group_attempt(state: dict[str, Any], identifier: str) -> tuple[str, dict[str, Any]]:
    group_attempts = state.setdefault("group_attempts", {})
    if not isinstance(group_attempts, dict):
        state["group_attempts"] = group_attempts = {}
    identifier_path = Path(identifier).expanduser()
    identifier_resolved = str(identifier_path.resolve()) if identifier_path.exists() else identifier
    for group_key, attempt in group_attempts.items():
        if not isinstance(attempt, dict):
            continue
        candidates = {
            str(group_key),
            str(attempt.get("action_id")),
            str(attempt.get("round")),
            str(attempt.get("group_id")),
            str(attempt.get("report_directory")),
            str(attempt.get("input")),
            str(attempt.get("report")),
        }
        if identifier in candidates or identifier_resolved in candidates:
            return str(group_key), attempt
    for action in state.get("next_actions", []):
        if not isinstance(action, dict) or action.get("kind") != "spawn-group-worker":
            continue
        group_key = f"{action.get('round')}:{action.get('group_id')}"
        report_path = Path(str(action.get("report", ""))).expanduser()
        report_directory = str(report_path.parent.resolve()) if report_path.parent.exists() else str(report_path.parent)
        candidates = {
            group_key,
            str(action.get("id")),
            str(action.get("round")),
            str(action.get("group_id")),
            str(action.get("input")),
            str(action.get("report")),
            report_directory,
        }
        if identifier not in candidates and identifier_resolved not in candidates:
            continue
        errors = _action_validity_errors(state, action)
        if errors:
            raise SystemExit("group action is stale: " + "; ".join(errors))
        attempt = group_attempts.setdefault(
            group_key,
            {
                "phase": VC_PROVING_PREPARING_PHASE,
                "round": action.get("round"),
                "group_id": action.get("group_id"),
                "action_id": action.get("id"),
                "status": "pending",
                "input": action.get("input"),
                "report": action.get("report"),
                "report_directory": report_directory,
            },
        )
        return group_key, attempt
    raise SystemExit(f"group attempt not found: {identifier}")


def _set_attempt_status(state: dict[str, Any], identifier: str, status: str, **extra: Any) -> tuple[str, dict[str, Any]]:
    attempt_id, attempt = _find_attempt(state, identifier)
    attempt["status"] = status
    attempt.update({key: value for key, value in extra.items() if value is not None})
    return attempt_id, attempt


def _set_group_attempt_status(state: dict[str, Any], identifier: str, status: str, **extra: Any) -> tuple[str, dict[str, Any]]:
    group_key, attempt = _find_group_attempt(state, identifier)
    attempt["status"] = status
    attempt.update({key: value for key, value in extra.items() if value is not None})
    return group_key, attempt


def mark_attempt_started(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    now = _utc()
    timing_now = _utc_timing()
    try:
        attempt_id, attempt = _find_attempt(state, args.attempt)
        action = _spawn_action_for_attempt(attempt)
        errors = _action_validity_errors(state, action)
        if errors:
            raise SystemExit("attempt is stale: " + "; ".join(errors))
        attempt["status"] = "running"
        attempt["started_at"] = now
        state["next_actions"] = [
            action
            for action in state.get("next_actions", [])
            if not (isinstance(action, dict) and action.get("attempt_id") == attempt_id)
        ]
        _append_event(
            run_root,
            state,
            "attempt-started",
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            attempt_id=attempt_id,
            details={"input": attempt.get("input"), "report": attempt.get("report")},
        )
        _append_run_timing_node(
            run_root,
            state,
            event="attempt-start",
            node_type="start",
            category="attempt",
            name=attempt_id,
            timestamp=timing_now,
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            attempt_id=attempt_id,
            timer_key=f"attempt:{attempt_id}",
        )
    except SystemExit as round_error:
        try:
            attempt_id, attempt = _find_group_attempt(state, args.attempt)
        except SystemExit:
            raise round_error
        action = {
            "id": attempt.get("action_id") or f"spawn-{attempt.get('round')}-{attempt.get('group_id')}",
            "kind": "spawn-group-worker",
            "phase": VC_PROVING_PREPARING_PHASE,
            "round": attempt.get("round"),
            "group_id": attempt.get("group_id"),
            "input": attempt.get("input"),
            "report": attempt.get("report"),
        }
        errors = _action_validity_errors(state, action)
        if errors:
            raise SystemExit("group attempt is stale: " + "; ".join(errors))
        attempt["status"] = "running"
        attempt["started_at"] = now
        state["next_actions"] = [
            action
            for action in state.get("next_actions", [])
            if not (
                isinstance(action, dict)
                and action.get("kind") == "spawn-group-worker"
                and action.get("round") == attempt.get("round")
                and action.get("group_id") == attempt.get("group_id")
            )
        ]
        _append_event(
            run_root,
            state,
            "group-worker-started",
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            group_id=attempt.get("group_id"),
            attempt_id=attempt_id,
            details={"input": attempt.get("input"), "report": attempt.get("report")},
        )
        _append_run_timing_node(
            run_root,
            state,
            event="group-worker-start",
            node_type="start",
            category="group_worker",
            name=attempt_id,
            timestamp=timing_now,
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            group_id=attempt.get("group_id"),
            attempt_id=attempt_id,
            timer_key=f"group_worker:{attempt_id}",
        )
    _save_state(run_root, state)
    print(json.dumps({"status": "running", "attempt_id": attempt_id}, indent=2))
    return 0


def mark_attempt_returned(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    now = _utc()
    timing_now = _utc_timing()
    try:
        attempt_id, attempt = _find_attempt(state, args.attempt)
        errors = _round_attempt_return_errors(state, attempt_id, attempt, args.result_status)
        if errors:
            raise SystemExit("attempt return is stale: " + "; ".join(errors))
        attempt["status"] = args.result_status
        attempt["returned_at"] = now
        _append_event(
            run_root,
            state,
            "attempt-returned",
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            attempt_id=attempt_id,
            details={"result_status": args.result_status, "report": attempt.get("report")},
        )
        _append_run_timing_node(
            run_root,
            state,
            event="attempt-end",
            node_type="end",
            category="attempt",
            name=attempt_id,
            timestamp=timing_now,
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            attempt_id=attempt_id,
            timer_key=f"attempt:{attempt_id}",
        )
    except SystemExit as round_error:
        try:
            attempt_id, attempt = _find_group_attempt(state, args.attempt)
        except SystemExit:
            raise round_error
        errors = _group_attempt_return_errors(state, attempt, args.result_status)
        if errors:
            raise SystemExit("group attempt return is stale: " + "; ".join(errors))
        attempt["status"] = args.result_status
        attempt["returned_at"] = now
        _append_event(
            run_root,
            state,
            "group-worker-returned",
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            group_id=attempt.get("group_id"),
            attempt_id=attempt_id,
            details={"result_status": args.result_status, "report": attempt.get("report")},
        )
        _append_run_timing_node(
            run_root,
            state,
            event="group-worker-end",
            node_type="end",
            category="group_worker",
            name=attempt_id,
            timestamp=timing_now,
            phase=attempt.get("phase"),
            round_id=attempt.get("round"),
            group_id=attempt.get("group_id"),
            attempt_id=attempt_id,
            timer_key=f"group_worker:{attempt_id}",
        )
    _save_state(run_root, state)
    print(json.dumps({"status": args.result_status, "attempt_id": attempt_id}, indent=2))
    return 0


def _attempt_report_path(attempt: Path) -> Path:
    if attempt.is_file():
        return attempt.resolve()
    for name in ("agent_report.json", "group_worker_report.json"):
        candidate = attempt / name
        if candidate.is_file():
            return candidate.resolve()
    raise SystemExit(f"attempt report not found: {attempt}")


def _input_path_for_report(report_path: Path) -> Path | None:
    if report_path.name == "agent_report.json":
        return report_path.with_name("agent_input.json")
    if report_path.name == "group_worker_report.json":
        return report_path.with_name("group_worker_input.json")
    return None


def _output_path_for_report(report_path: Path) -> Path | None:
    if report_path.name == "agent_report.json":
        return report_path.with_name("agent_output.txt")
    if report_path.name == "group_worker_report.json":
        return report_path.with_name("group_worker_output.txt")
    return None


def _allowed_output_roots(input_payload: dict[str, Any], report_path: Path) -> list[Path]:
    roots = [report_path.parent.resolve()]
    round_worktree = input_payload.get("round_worktree")
    if isinstance(round_worktree, str) and round_worktree:
        roots.append(Path(round_worktree).expanduser().resolve())
    group = input_payload.get("group") if isinstance(input_payload.get("group"), dict) else {}
    group_worktree = group.get("worktree_path")
    if isinstance(group_worktree, str) and group_worktree:
        roots.append(Path(group_worktree).expanduser().resolve())
    return roots


def check_output_note_payload(
    *,
    output_path: Path,
    input_payload: dict[str, Any],
    report_path: Path,
) -> dict[str, Any]:
    warnings: list[str] = []
    if not output_path.is_file():
        warnings.append(f"output note missing: {output_path}")
    else:
        data = output_path.read_bytes()
        if len(data) > 20 * 1024:
            warnings.append("output note exceeds 20KB")
        text = data.decode("utf-8", errors="replace")
        lines = text.splitlines()
        if not lines or lines[0].strip() != "# Reuse Note":
            warnings.append("first line must be # Reuse Note")
        if "Note kind: non-authoritative reuse note" not in text:
            warnings.append("missing note kind declaration")
        if "This file is not acceptance evidence." not in text:
            warnings.append("missing non-acceptance evidence declaration")
        forbidden_claims = [
            "controller accepted",
            "round accepted",
            "group accepted",
            "final-check passed",
        ]
        lowered = text.lower()
        for phrase in forbidden_claims:
            if phrase in lowered:
                warnings.append(f"output note contains over-authoritative claim: {phrase}")
        allowed_roots = _allowed_output_roots(input_payload, report_path)
        for match in re.finditer(r"(?<![A-Za-z0-9_])/[^\s`'\"),;]+", text):
            candidate = Path(match.group(0)).expanduser()
            try:
                resolved = candidate.resolve()
            except OSError:
                continue
            if not any(resolved == root or root in resolved.parents for root in allowed_roots):
                warnings.append(f"absolute path outside declared worktree/report roots: {candidate}")
                break
    return {
        "status": "passed" if not warnings else "warning",
        "checked_at": _utc(),
        "path": str(output_path),
        "kind": "non-authoritative-reuse-note",
        "acceptance_evidence": "no",
        "warnings": warnings,
    }


def check_output_note(args: argparse.Namespace) -> int:
    output_path = Path(args.path).expanduser().resolve()
    input_path = Path(args.input).expanduser().resolve() if args.input else None
    report_path = Path(args.report).expanduser().resolve() if args.report else output_path.with_name("agent_report.json")
    if not report_path.is_file() and output_path.name == "group_worker_output.txt":
        report_path = output_path.with_name("group_worker_report.json")
    input_payload = _json_load(input_path, {}) if input_path else {}
    if not isinstance(input_payload, dict):
        input_payload = {}
    result = check_output_note_payload(output_path=output_path, input_payload=input_payload, report_path=report_path)
    print(json.dumps(result, indent=2))
    return 0


def _has_compact_error_marker(result: dict[str, Any]) -> bool:
    if result.get("status") == "compact-error":
        return True
    if result.get("compact_error") or result.get("compact-error"):
        return True
    for key in ("blockers", "errors"):
        items = result.get(key)
        if not isinstance(items, list):
            continue
        for item in items:
            if isinstance(item, dict):
                if "compact_error" in item or "compact-error" in item:
                    return True
                marker = item.get("failure_class") or item.get("kind") or item.get("class") or item.get("status")
                if isinstance(marker, str) and marker.startswith("compact-error"):
                    return True
            elif isinstance(item, str) and "compact-error" in item:
                return True
    return False


def _compact_retry_key(report: dict[str, Any] | None, report_path: Path, attempt: dict[str, Any] | None) -> str:
    if report_path.name == "group_worker_report.json" and isinstance(report, dict):
        group = (
            report.get("agent_result", {}).get("vc_proving", {}).get("group", {})
            if isinstance(report.get("agent_result"), dict)
            else {}
        )
        group_id = str(report.get("group_id") or group.get("group_id") or report_path.parent.name)
        round_id = str(attempt.get("round") if attempt else report_path.parent.parent.name)
        return f"group:{round_id}:{group_id}"
    round_id = str(attempt.get("round") if attempt else report_path.parent.name)
    return f"round:{round_id}"


SOFT_BLOCKER_CLASSES = {
    "annotation-design-summary-missing",
    "diagnostic-hint-missing",
    "diagnostics-hint-missing",
    "diagnostics-missing",
    "future-proof-difficulty",
    "group-adjustment-needed",
    "group-plan-incomplete",
    "hard-proof",
    "helper-design-uncertain",
    "helper-missing",
    "helper-needed",
    "helper-not-yet-proved",
    "missing-diagnostic-hint",
    "needs-grouping",
    "needs-helper",
    "optional-reference-missing",
    "proof-difficulty",
    "proof-plan-incomplete",
    "proof-route-uncertain",
    "proof-route-unknown",
    "schema-warning",
    "worker-proof-risk",
}

HARD_BLOCKER_CLASSES = {
    "annotation-bug",
    "case-lib-contract-failed",
    "semantic-impossible",
    "source-goal-version-mismatch",
    "stale",
    "tool-unavailable",
    "toolchain-unavailable",
    "unprovable",
    "vc-not-provable",
}


def _normalized_class(value: Any) -> str:
    return str(value or "").strip().lower().replace("_", "-")


def _blocker_class_values(blocker: Any) -> list[str]:
    if not isinstance(blocker, dict):
        return []
    values: list[str] = []
    for key in (
        "failure_class",
        "kind",
        "class",
        "category",
        "judgment",
        "status",
        "reason_code",
        "blocker_class",
    ):
        normalized = _normalized_class(blocker.get(key))
        if normalized:
            values.append(normalized)
    for nested_key in ("blocked_witnesses", "witnesses", "items"):
        nested = blocker.get(nested_key)
        if isinstance(nested, list):
            for item in nested:
                values.extend(_blocker_class_values(item))
    return values


def _only_soft_blockers(blockers: list[Any]) -> bool:
    if not blockers:
        return False
    saw_soft = False
    for blocker in blockers:
        values = _blocker_class_values(blocker)
        if not values:
            return False
        if any(value in HARD_BLOCKER_CLASSES for value in values):
            return False
        soft_values = [value for value in values if value in SOFT_BLOCKER_CLASSES]
        if not soft_values:
            return False
        saw_soft = True
    return saw_soft


def _has_group_plan_artifact(vc_checking: dict[str, Any]) -> bool:
    for key in ("group_plan", "proof_group_plan"):
        plan = vc_checking.get(key)
        if isinstance(plan, dict) and isinstance(plan.get("proof_groups"), list) and plan.get("proof_groups"):
            return True
    for key in ("group_plan_path", "group_plan_file"):
        if str(vc_checking.get(key) or "").strip():
            return True
    return vc_checking.get("group_plan_ready") is True


def _has_group_manifest_artifact(vc_proving: dict[str, Any]) -> bool:
    for key in ("group_workers_manifest", "manifest"):
        value = vc_proving.get(key)
        if isinstance(value, dict) and isinstance(value.get("groups"), list):
            return True
        if isinstance(value, str) and value.strip():
            return True
    for key in ("group_workers_manifest_path", "manifest_path"):
        if str(vc_proving.get(key) or "").strip():
            return True
    return vc_proving.get("manifest_ready") is True or vc_proving.get("group_handoffs_ready") is True


def _materialize_inline_vc_checking_group_plan(report: dict[str, Any], report_path: Path) -> dict[str, Any] | None:
    vc_checking = _vc_checking_result(report)
    plan = vc_checking.get("group_plan")
    if not isinstance(plan, dict):
        plan = vc_checking.get("proof_group_plan")
    if not isinstance(plan, dict):
        return None
    plan_path = report_path.parent / "group_plan.json"
    if plan_path.is_file():
        return None
    write_json(plan_path, plan)
    repair = {
        "kind": "materialized-inline-group-plan",
        "source": str(report_path),
        "target": str(plan_path),
        "reason": "vc-checking report included an inline group_plan but the default group_plan.json artifact was missing",
    }
    report.setdefault("verification_result", {}).setdefault("controller_simple_repairs", []).append(repair)
    write_json(report_path, report)
    return repair


def _review_group(report: dict[str, Any], expected_source_goal_version: str | None) -> tuple[str, list[str]]:
    if isinstance(expected_source_goal_version, dict):
        expected_source_goal_version = expected_source_goal_version.get("digest")
    group = (
        report.get("agent_result", {})
        .get("vc_proving", {})
        .get("group", {})
        if isinstance(report.get("agent_result"), dict)
        else {}
    )
    errors: list[str] = []
    if not isinstance(group, dict):
        return "invalid-report", ["missing agent_result.vc_proving.group"]
    status = group.get("status")
    if _has_compact_error_marker(group):
        return "compact-error-with-no-progress", ["compact error reported"]
    if status == "stale":
        return "stale", ["group report is stale"]
    if group.get("source_goal_version") and group.get("source_goal_version") != expected_source_goal_version:
        return "stale", ["source_goal_version mismatch"]
    if status == "blocked":
        return "blocked", [json.dumps(item, sort_keys=True) for item in group.get("blockers", [])] or ["group blocked"]
    if group.get("source_goal_version") != expected_source_goal_version:
        errors.append("source_goal_version evidence is not acceptable")
    if status != "completed":
        errors.append("group status is not completed")
    namespace = group.get("helper_namespace") if isinstance(group.get("helper_namespace"), dict) else {}
    if namespace.get("policy") != "group-id-suffixed" or namespace.get("required") != "yes" or not namespace.get("suffix"):
        errors.append("helper_namespace evidence is not acceptable")
    if not isinstance(group.get("case_lib_added_declarations"), list):
        errors.append("case_lib_added_declarations evidence is not acceptable")
    if group.get("errors"):
        errors.append("group reported errors")
    if group.get("blockers"):
        errors.append("group reported blockers")
    verification = group.get("verification_result") if isinstance(group.get("verification_result"), dict) else {}
    coq = verification.get("coqc_check") if isinstance(verification.get("coqc_check"), dict) else {}
    if coq.get("source_goal_version") and coq.get("source_goal_version") != expected_source_goal_version:
        return "stale", ["coqc_check source_goal_version mismatch"]
    if coq.get("status") != "passed" or coq.get("source_goal_version") != expected_source_goal_version:
        errors.append("coqc_check evidence is not acceptable")
    return ("accepted" if not errors else "blocked", errors)


def _group_worker_result(report: dict[str, Any]) -> dict[str, Any]:
    result = report.get("agent_result") if isinstance(report.get("agent_result"), dict) else {}
    vc_proving = result.get("vc_proving") if isinstance(result.get("vc_proving"), dict) else {}
    group = vc_proving.get("group") if isinstance(vc_proving.get("group"), dict) else {}
    return group if isinstance(group, dict) else {}


def _annotation_result(report: dict[str, Any]) -> dict[str, Any]:
    result = report.get("agent_result") if isinstance(report.get("agent_result"), dict) else {}
    annotation = result.get("annotation") if isinstance(result.get("annotation"), dict) else {}
    return annotation if isinstance(annotation, dict) else {}


def _annotation_contract_errors(input_payload: dict[str, Any], annotation: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    required_lessons = (
        input_payload.get("required_lessons") if isinstance(input_payload.get("required_lessons"), list) else []
    )
    reviewed = (
        annotation.get("previous_attempts_reviewed")
        if isinstance(annotation.get("previous_attempts_reviewed"), list)
        else []
    )
    addressed = (
        annotation.get("prior_blockers_addressed")
        if isinstance(annotation.get("prior_blockers_addressed"), list)
        else []
    )
    lesson_ids = {str(item.get("id")) for item in required_lessons if isinstance(item, dict) and item.get("id")}
    covered: set[str] = set()
    for item in reviewed:
        if not isinstance(item, dict):
            continue
        for lesson_id in item.get("lessons_applied", []) if isinstance(item.get("lessons_applied"), list) else []:
            covered.add(str(lesson_id))
    for item in addressed:
        if not isinstance(item, dict) or not item.get("id"):
            continue
        if str(item.get("status")) in {"addressed", "completed", "yes"}:
            covered.add(str(item["id"]))
    missing = sorted(lesson_ids - covered)
    if missing:
        errors.append("required_lessons not covered: " + ", ".join(missing))

    reference_policy = (
        input_payload.get("reference_policy") if isinstance(input_payload.get("reference_policy"), dict) else {}
    )
    if reference_policy.get("must_log_file_reads") == "yes":
        summary = annotation.get("file_access_summary")
        if not isinstance(summary, dict):
            errors.append("file_access_summary is required by reference_policy")
        else:
            denied_touched = summary.get("denied_globs_touched")
            if denied_touched is not None and not isinstance(denied_touched, list):
                errors.append("file_access_summary.denied_globs_touched must be a list")
    return errors


def _review_annotation(report: dict[str, Any], input_payload: dict[str, Any] | None = None) -> tuple[str, list[str]]:
    annotation = _annotation_result(report)
    if not annotation:
        return "invalid-report", ["missing agent_result.annotation"]
    status = annotation.get("status")
    blockers = annotation.get("blockers") if isinstance(annotation.get("blockers"), list) else []
    ready = annotation.get("ready_for_annotation_check_round") is True
    contract_errors = _annotation_contract_errors(input_payload or {}, annotation) if input_payload else []
    if _has_compact_error_marker(annotation):
        return "compact-error-with-no-progress", ["compact error reported"]
    hard_contract_errors: list[str] = []
    if status == "completed" and ready:
        if hard_contract_errors:
            return "blocked", hard_contract_errors
        return "accepted-for-main-check", []
    if status == "completed":
        errors = []
        if not ready:
            errors.append("annotation completed without ready_for_annotation_check_round")
        if hard_contract_errors:
            return "blocked", hard_contract_errors
        if ready:
            return "accepted-for-main-check", []
        errors.extend(contract_errors)
        errors.extend(json.dumps(item, sort_keys=True) for item in blockers)
        return "blocked", errors or ["annotation completed but did not produce a ready candidate"]
    if status == "blocked":
        if ready:
            return "accepted-for-main-check", []
        return "blocked", contract_errors + ([json.dumps(item, sort_keys=True) for item in blockers] or ["annotation blocked"])
    if status == "stale":
        return "stale", ["annotation report is stale"]
    return "invalid-report", [f"unsupported annotation status: {status!r}"]


def _lesson_from_text(source_round: str, index: int, text: str, failure_class: str) -> dict[str, Any]:
    return {
        "id": f"{slug(source_round)}-{slug(failure_class)}-{index}",
        "source_round": source_round,
        "failure_class": failure_class,
        "must_address": text,
    }


def _vc_checking_result(report: dict[str, Any]) -> dict[str, Any]:
    result = report.get("agent_result") if isinstance(report.get("agent_result"), dict) else {}
    if result.get("phase") == "vc-checking":
        return result
    vc_checking = result.get("vc_checking") if isinstance(result.get("vc_checking"), dict) else {}
    return vc_checking if isinstance(vc_checking, dict) else {}


def _source_goal_digest(value: Any) -> str | None:
    if isinstance(value, dict):
        digest = value.get("digest")
        return str(digest) if digest else None
    if value:
        return str(value)
    return None


def _review_vc_checking(
    report: dict[str, Any],
    *,
    expected_source_goal_version: Any,
) -> tuple[str, list[str]]:
    vc_checking = _vc_checking_result(report)
    if not vc_checking:
        return "invalid-report", ["missing agent_result.vc_checking"]
    expected = _source_goal_digest(expected_source_goal_version)
    errors: list[str] = []
    actual = _source_goal_digest(vc_checking.get("source_goal_version"))
    if expected and actual and actual != expected:
        return "stale", ["source_goal_version mismatch"]
    blockers = vc_checking.get("blockers") if isinstance(vc_checking.get("blockers"), list) else []
    status = vc_checking.get("status")
    if _has_compact_error_marker(vc_checking):
        return "compact-error-with-no-progress", ["compact error reported"]
    if status == "stale":
        return "stale", ["vc-checking report is stale"]
    if status == "completed":
        if expected and actual != expected:
            errors.append("source_goal_version evidence is not acceptable")
        return ("blocked", errors) if errors else ("accepted-for-main-check", [])
    if status == "blocked":
        if _only_soft_blockers(blockers) and _has_group_plan_artifact(vc_checking):
            return "accepted-for-main-check", []
        return "blocked", errors + [json.dumps(item, sort_keys=True) for item in blockers] or ["vc-checking blocked"]
    return "invalid-report", errors + ["vc-checking result is not ready for main-owned check"]


def _review_vc_proving(report: dict[str, Any], *, expected_source_goal_version: Any) -> tuple[str, list[str]]:
    result = report.get("agent_result") if isinstance(report.get("agent_result"), dict) else {}
    vc_proving = result.get("vc_proving") if isinstance(result.get("vc_proving"), dict) else {}
    if not isinstance(vc_proving, dict) or not vc_proving:
        return "invalid-report", ["missing agent_result.vc_proving"]
    expected = _source_goal_digest(expected_source_goal_version)
    errors: list[str] = []
    actual = _source_goal_digest(vc_proving.get("source_goal_version"))
    if expected and actual and actual != expected:
        return "stale", ["source_goal_version mismatch"]
    blockers = vc_proving.get("blockers") if isinstance(vc_proving.get("blockers"), list) else []
    status = vc_proving.get("status")
    if _has_compact_error_marker(vc_proving):
        return "compact-error-with-no-progress", ["compact error reported"]
    if status == "stale":
        return "stale", ["vc-proving report is stale"]
    if status == "completed":
        if expected and actual != expected:
            errors.append("source_goal_version evidence is not acceptable")
        return ("blocked", errors) if errors else ("accepted-for-main-check", [])
    if status == "blocked":
        if _only_soft_blockers(blockers) and _has_group_manifest_artifact(vc_proving):
            return "accepted-for-main-check", []
        return "blocked", errors + [json.dumps(item, sort_keys=True) for item in blockers] or ["vc-proving blocked"]
    return "invalid-report", errors + ["vc-proving result is not ready for group-worker scheduling"]


def _vc_checking_recommends_annotation(vc_checking: dict[str, Any]) -> bool:
    for blocker in vc_checking.get("blockers", []) if isinstance(vc_checking.get("blockers"), list) else []:
        if not isinstance(blocker, dict):
            continue
        if (
            blocker.get("recommended_next_phase") == "annotation"
            or blocker.get("recommended_return") == "annotation"
            or blocker.get("blocker_class") == "annotation-bug"
        ):
            return True
        for witness in blocker.get("blocked_witnesses", []) if isinstance(blocker.get("blocked_witnesses"), list) else []:
            if isinstance(witness, dict) and witness.get("recommended_next_phase") == "annotation":
                return True
    for blocker in vc_checking.get("blockers", []) if isinstance(vc_checking.get("blockers"), list) else []:
        if isinstance(blocker, dict) and blocker.get("kind") == "annotation-bug":
            return True
    nested = vc_checking.get("vc_checking") if isinstance(vc_checking.get("vc_checking"), dict) else {}
    if nested.get("recommended_next_phase") == "annotation":
        return True
    group_plan = nested.get("group_plan") if isinstance(nested.get("group_plan"), dict) else {}
    for blocker in group_plan.get("blockers", []) if isinstance(group_plan.get("blockers"), list) else []:
        if isinstance(blocker, dict) and blocker.get("kind") == "annotation-bug":
            return True
    return False


def _lessons_from_report(source_round: str, report: dict[str, Any]) -> list[dict[str, Any]]:
    annotation = _annotation_result(report)
    vc_checking = _vc_checking_result(report)
    group_worker = _group_worker_result(report)
    lessons: list[dict[str, Any]] = []
    index = 1
    for blocker in annotation.get("blockers", []) if isinstance(annotation.get("blockers"), list) else []:
        if not isinstance(blocker, dict):
            continue
        failure_class = str(blocker.get("kind") or blocker.get("failure_class") or "annotation-blocker")
        message = str(blocker.get("message") or blocker)
        lessons.append(_lesson_from_text(source_round, index, message, failure_class))
        index += 1
    checking = annotation.get("annotation_checking") if isinstance(annotation.get("annotation_checking"), dict) else {}
    for item in checking.get("required_rework", []) if isinstance(checking.get("required_rework"), list) else []:
        lessons.append(_lesson_from_text(source_round, index, str(item), "annotation-checking-failed"))
        index += 1
    checking_evidence = (
        annotation.get("annotation_checking_evidence")
        if isinstance(annotation.get("annotation_checking_evidence"), dict)
        else {}
    )
    for item in checking_evidence.get("rework_plan", []) if isinstance(checking_evidence.get("rework_plan"), list) else []:
        if not isinstance(item, dict):
            lessons.append(_lesson_from_text(source_round, index, str(item), "annotation-checking-failed"))
        else:
            lessons.append(
                _lesson_from_text(
                    source_round,
                    index,
                    str(item.get("message") or item),
                    str(item.get("failure_class") or "annotation-checking-failed"),
                )
            )
        index += 1
    for blocker in vc_checking.get("blockers", []) if isinstance(vc_checking.get("blockers"), list) else []:
        if not isinstance(blocker, dict):
            continue
        failure_class = str(blocker.get("failure_class") or blocker.get("kind") or "vc-checking-blocker")
        witnesses = blocker.get("blocked_witnesses") if isinstance(blocker.get("blocked_witnesses"), list) else []
        if not witnesses:
            message = str(blocker.get("message") or blocker)
            lesson = _lesson_from_text(source_round, index, message, failure_class)
            if vc_checking.get("source_goal_version"):
                lesson["source_goal_version"] = str(vc_checking.get("source_goal_version"))
            lessons.append(lesson)
            index += 1
            continue
        for witness in witnesses:
            if not isinstance(witness, dict):
                lesson = _lesson_from_text(source_round, index, str(witness), failure_class)
            else:
                parts = [
                    str(blocker.get("message") or "").strip(),
                    str(witness.get("reason") or "").strip(),
                    str(witness.get("missing_or_wrong_fact") or "").strip(),
                    str(witness.get("counterexample") or "").strip(),
                ]
                message = " ".join(part for part in parts if part)
                lesson = _lesson_from_text(source_round, index, message or str(witness), failure_class)
                for key in (
                    "witness_name",
                    "target_symbol",
                    "counterexample",
                    "missing_or_wrong_fact",
                    "recommended_next_phase",
                ):
                    if witness.get(key) is not None:
                        lesson[key] = witness.get(key)
            if vc_checking.get("source_goal_version"):
                lesson["source_goal_version"] = str(vc_checking.get("source_goal_version"))
            lessons.append(lesson)
            index += 1
    for blocker in group_worker.get("blockers", []) if isinstance(group_worker.get("blockers"), list) else []:
        if not isinstance(blocker, dict):
            continue
        failure_class = str(blocker.get("failure_class") or blocker.get("kind") or "group-worker-blocker")
        parts = [
            str(blocker.get("summary") or blocker.get("message") or "").strip(),
            str(blocker.get("why_local_helper_is_insufficient") or "").strip(),
            str(blocker.get("suggested_upstream_repair") or "").strip(),
        ]
        message = " ".join(part for part in parts if part) or str(blocker)
        lesson = _lesson_from_text(source_round, index, message, failure_class)
        if blocker.get("witness") is not None:
            lesson["witness_name"] = blocker.get("witness")
        if group_worker.get("source_goal_version"):
            lesson["source_goal_version"] = str(group_worker.get("source_goal_version"))
        lesson["recommended_next_phase"] = "annotation"
        lessons.append(lesson)
        index += 1
    if not lessons:
        lessons.append(_lesson_from_text(source_round, 1, "Review previous annotation blocker before retry.", "annotation-retry"))
    return lessons


def _coq_declaration_names(text: str) -> list[dict[str, str]]:
    declarations: list[dict[str, str]] = []
    pattern = re.compile(r"^\s*(Definition|Fixpoint|Inductive|Lemma|Theorem|Record)\s+([A-Za-z_][A-Za-z0-9_']*)")
    for line in text.splitlines():
        match = pattern.match(line)
        if match:
            declarations.append({"kind": match.group(1), "name": match.group(2)})
    return declarations


def _annotation_design_summary(
    report: dict[str, Any],
    *,
    round_worktree: Path,
    target_files: dict[str, str],
    problem_context: dict[str, Any],
) -> dict[str, Any]:
    annotation = _annotation_result(report)
    provided = annotation.get("annotation_design_summary")
    if isinstance(provided, dict):
        return provided
    case_lib_path = round_worktree / target_files["case_lib"]
    declarations: list[dict[str, str]] = []
    case_lib_digest = None
    if case_lib_path.is_file():
        text = case_lib_path.read_text(encoding="utf-8")
        declarations = _coq_declaration_names(text)
        case_lib_digest = _file_digest(case_lib_path)
    return {
        "schema_version": "qcp-annotation-design-summary/v1",
        "source": "controller-fallback",
        "case_lib_spec_declarations": declarations,
        "case_lib_sha256": case_lib_digest,
        "hidden_properties": problem_context.get("preferred_hidden_properties", []),
        "known_risks": annotation.get("known_risks", []) if isinstance(annotation.get("known_risks"), list) else [],
        "qcp_repair_history": annotation.get("self_reworkable_failures", [])
        if isinstance(annotation.get("self_reworkable_failures"), list)
        else [],
        "changed_files": annotation.get("changed_files", []) if isinstance(annotation.get("changed_files"), list) else [],
    }


def _previous_attempt_record(source_round: str, attempt: dict[str, Any], report_path: Path) -> dict[str, Any]:
    output_name = "group_worker_output.txt" if report_path.name == "group_worker_report.json" else "agent_output.txt"
    record = {
        "round": source_round,
        "report": str(report_path),
        "output": str(report_path.with_name(output_name)),
        "worktree": attempt.get("worktree"),
        "allowed_use": "read-only-analysis",
        "formal_copy_allowed": "no",
    }
    return record


def _resolve_retry_previous_attempt(state: dict[str, Any], identifier: str) -> tuple[str, dict[str, Any], Path]:
    candidate = Path(identifier).expanduser()
    if candidate.name == "group_worker_report.json" and candidate.is_file():
        report_path = candidate.resolve()
        report_payload = _json_load(report_path, {})
        group = _group_worker_result(report_payload) if isinstance(report_payload, dict) else {}
        group_id = str(group.get("group_id") or report_payload.get("group_id") or report_path.parent.name)
        round_id = report_path.parents[2].name if len(report_path.parents) >= 3 else report_path.parent.name
        parent_attempt: dict[str, Any] = {}
        for attempt in state.get("attempts", {}).values():
            if isinstance(attempt, dict) and attempt.get("round") == round_id and str(attempt.get("phase")) in VC_PROVING_PHASE_ALIASES:
                parent_attempt = attempt
                break
        input_payload = _json_load(report_path.with_name("group_worker_input.json"), {})
        input_group = input_payload.get("group") if isinstance(input_payload.get("group"), dict) else {}
        previous_attempt = dict(parent_attempt)
        previous_attempt.update(
            {
                "phase": "group-worker",
                "round": f"{round_id}/{group_id}",
                "report": str(report_path),
                "report_directory": str(report_path.parent),
                "worktree": input_group.get("worktree_path") or previous_attempt.get("worktree"),
            }
        )
        return f"group:{round_id}:{group_id}", previous_attempt, report_path
    previous_attempt_id, previous_attempt = _find_attempt(state, identifier)
    return previous_attempt_id, previous_attempt, Path(str(previous_attempt.get("report", "")))


def retry_round(args: argparse.Namespace) -> int:
    if args.phase not in {"annotation", "vc-checking"}:
        raise SystemExit("retry-round supports only --phase annotation or vc-checking; vc-proving-preparing errors are reported directly to the main agent")
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous_phase = str(state.get("phase") or "")
    previous_attempt_id, previous_attempt, previous_report = _resolve_retry_previous_attempt(state, args.previous_attempt)
    previous_round = str(previous_attempt.get("round") or args.previous_attempt)
    previous_report_payload = _json_load(previous_report, {}) if previous_report.is_file() else {}
    if not isinstance(previous_report_payload, dict):
        previous_report_payload = {}
    vc_checking = _vc_checking_result(previous_report_payload)
    group_worker = _group_worker_result(previous_report_payload)
    source_worktree = Path(str(state["main_worktree"]))
    annotation_source_annotated = False
    if args.phase == "vc-checking":
        accepted_annotation = state.get("accepted_rounds", {}).get("annotation")
        if not isinstance(accepted_annotation, dict) or not accepted_annotation.get("worktree"):
            raise SystemExit("vc-checking retry requires an accepted annotation round")
        source_worktree = Path(str(accepted_annotation["worktree"]))
    elif str(previous_attempt.get("phase")) == "vc-checking" and _vc_checking_recommends_annotation(vc_checking):
        current_source_goal = state.get("source_goal_version")
        current_source_goal_digest = (
            str(current_source_goal.get("digest")) if isinstance(current_source_goal, dict) else str(current_source_goal or "")
        )
        previous_source_goal_digest = _source_goal_digest(vc_checking.get("source_goal_version")) or ""
        if previous_source_goal_digest and previous_source_goal_digest != current_source_goal_digest:
            raise SystemExit("annotation retry from vc-checking has stale source_goal_version")
        accepted_annotation = state.get("accepted_rounds", {}).get("annotation")
        if not isinstance(accepted_annotation, dict) or not accepted_annotation.get("worktree"):
            raise SystemExit("annotation retry from vc-checking requires an accepted annotation round")
        source_worktree = Path(str(accepted_annotation["worktree"]))
        annotation_source_annotated = True
    elif args.phase == "annotation" and str(previous_attempt.get("phase")) in VC_PROVING_PHASE_ALIASES.union({"group-worker"}):
        current_source_goal = state.get("source_goal_version")
        current_source_goal_digest = (
            str(current_source_goal.get("digest")) if isinstance(current_source_goal, dict) else str(current_source_goal or "")
        )
        previous_source_goal_digest = _source_goal_digest(
            group_worker.get("source_goal_version")
            or previous_report_payload.get("source_goal_version")
            or previous_report_payload.get("agent_result", {}).get("vc_proving", {}).get("source_goal_version")
        )
        if previous_source_goal_digest and previous_source_goal_digest != current_source_goal_digest:
            raise SystemExit("annotation retry from vc-proving/group-worker has stale source_goal_version")
        accepted_annotation = state.get("accepted_rounds", {}).get("annotation")
        if not isinstance(accepted_annotation, dict) or not accepted_annotation.get("worktree"):
            raise SystemExit("annotation retry from vc-proving/group-worker requires an accepted annotation round")
        source_worktree = Path(str(accepted_annotation["worktree"]))
        annotation_source_annotated = True
    existing_rounds = [
        str(attempt.get("round"))
        for attempt in state.get("attempts", {}).values()
        if isinstance(attempt, dict) and str(attempt.get("phase")) == args.phase
    ]
    next_index = 1
    for round_name in existing_rounds:
        suffix = round_name.rsplit("-r", 1)
        if len(suffix) == 2 and suffix[1].isdigit():
            next_index = max(next_index, int(suffix[1]) + 1)
    round_id = f"{slug(state['case'])}-{args.phase}-r{next_index}"
    while f"{round_id}-attempt-1" in state.get("attempts", {}):
        next_index += 1
        round_id = f"{slug(state['case'])}-{args.phase}-r{next_index}"
    previous_attempts = [_previous_attempt_record(previous_round, previous_attempt, previous_report)]
    required_lessons = _lessons_from_report(previous_round, previous_report_payload)
    previous_status = _annotation_result(previous_report_payload).get("status") if previous_report_payload else None
    previous_blockers = _annotation_result(previous_report_payload).get("blockers", []) if previous_report_payload else []
    if vc_checking:
        previous_status = vc_checking.get("status")
        previous_blockers = vc_checking.get("blockers", [])
    if group_worker:
        previous_status = group_worker.get("status")
        previous_blockers = group_worker.get("blockers", [])
    prior_failure_summaries = [
        {
            "round": previous_round,
            "attempt_id": previous_attempt_id,
            "reason": args.reason,
            "status": previous_status or previous_attempt.get("status"),
            "blockers": previous_blockers,
        }
    ]
    if vc_checking.get("source_goal_version"):
        prior_failure_summaries[0]["source_goal_version"] = vc_checking.get("source_goal_version")
    if group_worker.get("source_goal_version"):
        prior_failure_summaries[0]["source_goal_version"] = group_worker.get("source_goal_version")
    attempt = _init_round_attempt(
        run_root=run_root,
        state=state,
        phase=args.phase,
        round_id=round_id,
        source_worktree=source_worktree,
        attempt_index=1,
        previous_attempts=previous_attempts,
        required_lessons=required_lessons,
        prior_failure_summaries=prior_failure_summaries,
        annotation_source_annotated=annotation_source_annotated,
    )
    attempt_id = attempt["attempt_id"]
    attempt["previous_attempt"] = previous_attempt_id
    state["phase"] = args.phase
    state["next_actions"] = [
        {
            "id": f"spawn-{attempt_id}",
            "kind": "spawn-attempt",
            "phase": args.phase,
            "attempt_id": attempt_id,
            "input": attempt["input"],
            "report": attempt["report"],
        }
    ]
    state["current_blockers"] = [
        {
            "failure_class": args.reason,
            "attempt": str(previous_report),
            "retry_round": round_id,
            "message": "annotation retry created by controller after terminal previous attempt",
        }
    ]
    _append_event(
        run_root,
        state,
        "retry-created",
        phase=args.phase,
        round_id=round_id,
        attempt_id=attempt_id,
        details={
            "reason": args.reason,
            "previous_attempt": previous_attempt_id,
            "previous_round": previous_round,
            "parent_worktree": str(source_worktree.resolve()),
            "input": attempt["input"],
            "report": attempt["report"],
        },
    )
    _append_phase_transition_timing(
        run_root,
        state,
        previous_phase=previous_phase,
        next_phase=str(state.get("phase") or ""),
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "retry-created",
                "round": round_id,
                "attempt_id": attempt_id,
                "input": attempt["input"],
                "report": attempt["report"],
            },
            indent=2,
        )
    )
    return 0


def review_attempt(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    report_path = _attempt_report_path(Path(args.attempt).expanduser())
    attempt_identifier = str(report_path.parent)
    try:
        attempt_id, attempt = _find_attempt(state, attempt_identifier)
    except SystemExit:
        attempt_id, attempt = attempt_identifier, {}
    input_path = Path(str(attempt.get("input", ""))) if attempt.get("input") else _input_path_for_report(report_path)
    input_payload = _json_load(input_path, {}) if input_path and input_path.is_file() else {}
    if not isinstance(input_payload, dict):
        input_payload = {}
    sync_vc_proving_attempt: dict[str, Any] | None = None
    try:
        report = _json_load(report_path)
    except json.JSONDecodeError as exc:
        report = None
        errors = [f"invalid JSON: {exc}"]
    else:
        errors = []
    round_review_errors: list[str] = []
    if report_path.name == "agent_report.json":
        round_review_errors = _round_report_review_errors(state, attempt_id, attempt, report_path)
    if not isinstance(report, dict):
        status = "invalid-report"
    elif round_review_errors:
        status = "stale"
        errors = round_review_errors
    elif report_path.name == "group_worker_report.json":
        group_entry, parent_attempt, manifest_path, lineage_errors = _group_manifest_entry_for_report(state, report_path)
        if lineage_errors:
            status, errors = "stale", lineage_errors
        else:
            group_id_from_manifest = str(group_entry.get("group_id")) if isinstance(group_entry, dict) else ""
            group_result = _group_worker_result(report)
            group_id_from_report = str(group_result.get("group_id") or report.get("group_id") or "")
            if group_id_from_manifest != group_id_from_report:
                status, errors = "stale", ["group report group_id does not match current manifest"]
            else:
                status, errors = _review_group(report, _current_source_goal_digest(state))
            if parent_attempt:
                sync_vc_proving_attempt = parent_attempt
        if status == "accepted":
            group_id = str(
                report.get("group_id")
                or report.get("agent_result", {}).get("vc_proving", {}).get("group", {}).get("group_id")
            )
            handoff_files = group_entry.get("handoff_files") if isinstance(group_entry.get("handoff_files"), dict) else {}
            state.setdefault("group_acceptance", {})[group_id] = {
                "status": "accepted",
                "round": parent_attempt.get("round") if parent_attempt else None,
                "attempt_id": parent_attempt.get("attempt_id") if parent_attempt else None,
                "source_goal_version_digest": _current_source_goal_digest(state),
                "manifest": str(manifest_path.resolve()) if manifest_path else None,
                "report": str(report_path),
                "input": str(handoff_files.get("input")) if handoff_files.get("input") else None,
                "report_directory": str(report_path.parent),
                "worktree": group_entry.get("worktree_path") if isinstance(group_entry, dict) else None,
                "accepted_at": _utc(),
            }
    elif report_path.name == "agent_report.json" and _annotation_result(report):
        status, errors = _review_annotation(report, input_payload if isinstance(input_payload, dict) else None)
        if status == "accepted-for-main-check":
            report.setdefault("verification_result", {})["annotation_review"] = {
                "status": status,
                "reviewed_at": _utc(),
            }
            write_json(report_path, report)
    else:
        result = report.get("agent_result") if isinstance(report.get("agent_result"), dict) else {}
        vc_checking = result.get("vc_checking") if isinstance(result.get("vc_checking"), dict) else {}
        vc_proving = result.get("vc_proving") if isinstance(result.get("vc_proving"), dict) else {}
        if vc_checking:
            status, errors = _review_vc_checking(report, expected_source_goal_version=state.get("source_goal_version"))
        elif vc_proving:
            status, errors = _review_vc_proving(report, expected_source_goal_version=state.get("source_goal_version"))
        elif _has_compact_error_marker(result):
            status = "compact-error-with-no-progress"
            errors = ["compact error reported"]
        else:
            status = "invalid-report"
            errors = ["attempt report is not completed"]
    if isinstance(report, dict):
        output_path = _output_path_for_report(report_path)
        if output_path is not None:
            output_check = check_output_note_payload(
                output_path=output_path,
                input_payload=input_payload,
                report_path=report_path,
            )
            report.setdefault("verification_result", {})["output_note_check"] = output_check
            write_json(report_path, report)
    if status in {"accepted", "accepted-for-main-check"}:
        if (
            status == "accepted-for-main-check"
            and isinstance(report, dict)
            and report_path.name == "agent_report.json"
            and _vc_checking_result(report)
        ):
            _materialize_inline_vc_checking_group_plan(report, report_path)
        state["current_blockers"] = []
        if attempt and report_path.name == "agent_report.json":
            attempt["status"] = "ready-for-main-check" if status == "accepted-for-main-check" else "accepted"
        _append_event(
            run_root,
            state,
            "attempt-reviewed",
            phase=attempt.get("phase") if attempt else None,
            round_id=attempt.get("round") if attempt else None,
            attempt_id=attempt_id,
            details={"status": status, "report": str(report_path)},
        )
        if sync_vc_proving_attempt:
            _sync_vc_proving_next_actions(state, sync_vc_proving_attempt)
        elif attempt and str(attempt.get("phase")) in VC_PROVING_PHASE_ALIASES:
            _sync_vc_proving_next_actions(state, attempt)
    else:
        blocker = {"failure_class": status, "attempt": str(report_path), "errors": errors}
        event_name = "attempt-review-blocked"
        if status == "compact-error-with-no-progress":
            key = _compact_retry_key(report if isinstance(report, dict) else None, report_path, attempt if attempt else None)
            compact_reports = state.setdefault("compact_attempt_reports", {}).setdefault(key, [])
            if str(report_path) not in compact_reports:
                compact_reports.append(str(report_path))
            compact_count = len(compact_reports)
            state.setdefault("compact_counts", {})[key] = compact_count
            max_compact = int(state.get("max_compact_attempts", 3))
            exhausted = compact_count >= max_compact
            blocker.update(
                {
                    "compact_retry_key": key,
                    "compact_attempt_count": compact_count,
                    "max_compact_attempts": max_compact,
                    "controller_judgment": "blocked" if exhausted else "retryable",
                }
            )
            event_name = "attempt-review-compact-error"
            if exhausted:
                status = "compact-error-retry-exhausted"
                blocker["failure_class"] = status
                blocker["message"] = "compact retry attempts exhausted; controller marks final blocker"
            state["current_blockers"] = [
                item
                for item in state.get("current_blockers", [])
                if not (isinstance(item, dict) and item.get("compact_retry_key") == key)
            ]
        if blocker not in state.setdefault("current_blockers", []):
            state["current_blockers"].append(blocker)
        if attempt:
            attempt["status"] = status
        _append_event(
            run_root,
            state,
            event_name,
            phase=attempt.get("phase") if attempt else None,
            round_id=attempt.get("round") if attempt else None,
            attempt_id=attempt_id,
            details=blocker,
        )
    _save_state(run_root, state)
    if args.run_main_check_if_ready and status == "accepted-for-main-check" and attempt:
        if attempt.get("phase") == "annotation":
            return annotation_check_round(
                argparse.Namespace(
                    main_worktree_root=str(main_root),
                    run=args.run,
                    round=str(attempt["round"]),
                )
            )
        if attempt.get("phase") == "vc-checking":
            return vc_checking_check_round(
                argparse.Namespace(
                    main_worktree_root=str(main_root),
                    run=args.run,
                    round=str(attempt["round"]),
                    manual_file=None,
                    group_plan=None,
                )
            )
    print(json.dumps({"status": status, "errors": errors, "report": str(report_path)}, indent=2))
    return 0 if status in {"accepted", "accepted-for-main-check"} else 1


def _verify_group_plan(manual: Path, plan_path: Path, source_goal_version: str) -> dict[str, Any]:
    text = manual.read_text(encoding="utf-8")
    _prelude, lemmas = parse_manual_file(text)
    ensure_unique_lemma_names(lemmas)
    plan = load_group_plan(plan_path)
    target_witnesses = [str(lemma["name"]) for lemma in lemmas]
    grouping_policy = _controller_grouping_policy(target_witnesses)
    group_plan_errors = _group_plan_policy_errors(plan, target_witnesses, grouping_policy)
    if group_plan_errors:
        raise SystemExit("group plan violates controller policy: " + "; ".join(group_plan_errors))
    group_entries_from_plan(
        lemmas,
        {
            **plan,
            "controller_verified": True,
            "source_goal_version": source_goal_version,
            "target_witnesses": target_witnesses,
            "grouping_policy": grouping_policy,
        },
        require_controller_verified=True,
        source_goal_version=source_goal_version,
    )
    plan["controller_verified"] = True
    plan["source_goal_version"] = source_goal_version
    plan["target_witnesses"] = target_witnesses
    plan["grouping_policy"] = grouping_policy
    write_json(plan_path, plan)
    return plan


def _controller_grouping_policy(target_witnesses: list[str]) -> dict[str, Any]:
    max_per_group = DEFAULT_MAX_WITNESSES_PER_GROUP
    return {
        "schema_version": "qcp-grouping-policy/v1",
        "controller_policy": "bounded-witness-groups/v1",
        "controller_enforced": "yes",
        "target_witness_count": len(target_witnesses),
        "max_witnesses_per_group": max_per_group,
        "single_group_allowed_only_if_target_witness_count_lte": max_per_group,
        "oversized_group_rejected": "yes",
    }


def _group_plan_policy_errors(
    plan: dict[str, Any],
    target_witnesses: list[str],
    policy: dict[str, Any],
) -> list[str]:
    errors: list[str] = []
    max_per_group = int(policy.get("max_witnesses_per_group") or DEFAULT_MAX_WITNESSES_PER_GROUP)
    groups = plan.get("proof_groups") if isinstance(plan.get("proof_groups"), list) else []
    if len(target_witnesses) > max_per_group and len(groups) == 1:
        errors.append(
            f"single proof group cannot cover {len(target_witnesses)} witnesses; "
            f"max_witnesses_per_group is {max_per_group}"
        )
    for group in groups:
        if not isinstance(group, dict):
            continue
        witnesses = [str(item) for item in group.get("witness_names", [])] if isinstance(group.get("witness_names"), list) else []
        if len(witnesses) > max_per_group:
            errors.append(
                f"proof group `{group.get('group_id')}` has {len(witnesses)} witnesses; "
                f"max_witnesses_per_group is {max_per_group}"
            )
    return errors


def verify_round(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    if not args.manual_file or not args.group_plan:
        raise SystemExit("verify-round currently requires --manual-file and --group-plan")
    manual = Path(args.manual_file).expanduser().resolve()
    plan_path = Path(args.group_plan).expanduser().resolve()
    source_goal_version = args.source_goal_version or state.get("source_goal_version")
    if isinstance(source_goal_version, dict):
        source_goal_version = str(source_goal_version.get("digest"))
    if not source_goal_version:
        raise SystemExit("verify-round requires --source-goal-version or current run source_goal_version")
    plan = _verify_group_plan(manual, plan_path, str(source_goal_version))
    _append_event(run_root, state, "round-verified", round_id=args.round, details={"group_plan": str(plan_path)})
    _save_state(run_root, state)
    print(json.dumps({"status": "accepted", "group_plan": str(plan_path), "target_witnesses": plan["target_witnesses"]}, indent=2))
    return 0


def annotation_check_round(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous_phase = str(state.get("phase") or "")
    attempt_id, attempt = _find_attempt(state, args.round)
    round_worktree = Path(str(attempt["worktree"])).resolve()
    report_path = Path(str(attempt["report"])).resolve()
    input_payload = _json_load(Path(str(attempt["input"])), {})
    report = _json_load(report_path, {})
    review_status, review_errors = _review_annotation(report, input_payload if isinstance(input_payload, dict) else None)
    if review_status != "accepted-for-main-check":
        raise SystemExit("annotation-check-round requires a round reviewed as accepted-for-main-check: " + "; ".join(review_errors))
    target_files = _target_files_for_state(state)
    canonical_symexec = _run_canonical_symexec(state, round_worktree, target_files)
    if canonical_symexec.get("status") == "failed":
        report.setdefault("verification_result", {})["annotation_check_round"] = {
            "status": "failed",
            "checked_at": _utc(),
            "canonical_symexec_evidence": canonical_symexec,
        }
        report["status"] = "blocked"
        report["terminal"] = "yes"
        report["blockers"] = [
            {
                "failure_class": "canonical-symexec-failed",
                "message": "canonical symbolic execution failed during annotation-check-round",
            }
        ]
        write_json(report_path, report)
        raise SystemExit("canonical symbolic execution failed during annotation-check-round")
    diagnostics_split = _split_manual_diagnostics_for_workspace(round_worktree, target_files)
    source_version = _source_version_for_workspace(state, round_worktree, annotated=True)
    source_goal_version = _source_goal_version_for_workspace(round_worktree, target_files)
    design_summary = _annotation_design_summary(
        report,
        round_worktree=round_worktree,
        target_files=target_files,
        problem_context=_normalized_problem_context(state),
    )
    report["kind"] = "annotation"
    report["status"] = "accepted"
    report["terminal"] = "yes"
    report["blockers"] = []
    report.setdefault("verification_result", {})["annotation_check_round"] = {
        "status": "passed",
        "accepted_at": _utc(),
        "source_version": source_version,
        "source_goal_version": source_goal_version,
        "annotation_design_summary": design_summary,
        "canonical_symexec_evidence": canonical_symexec,
        "diagnostics_split": diagnostics_split,
    }
    write_json(report_path, report)
    state["source_version"] = source_version
    state["source_goal_version"] = source_goal_version
    state["annotation_design_summary"] = design_summary
    state.setdefault("accepted_rounds", {})["annotation"] = _round_acceptance_payload(
        "annotation",
        str(attempt["round"]),
        attempt,
        source_version=source_version,
        source_goal_version=source_goal_version,
    )
    _stale_downstream_acceptance(
        state,
        from_phase="annotation",
        reason="accepted annotation round replaced upstream formal source",
    )
    attempt["status"] = "accepted"
    state["phase"] = "vc-checking"
    state["current_blockers"] = []
    state["next_actions"] = []
    _append_event(
        run_root,
        state,
        "round-accepted",
        phase="annotation",
        round_id=str(attempt["round"]),
        attempt_id=attempt_id,
        details={
            "main_owned_action": "annotation-check-round",
            "report": str(report_path),
            "manual_obligation_count": len(source_goal_version.get("target_witnesses", [])),
        },
    )
    _append_phase_transition_timing(
        run_root,
        state,
        previous_phase=previous_phase,
        next_phase=str(state.get("phase") or ""),
    )
    _save_state(run_root, state)
    print(json.dumps({"status": "accepted", "round": attempt["round"]}, indent=2))
    return 0


def vc_checking_check_round(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous_phase = str(state.get("phase") or "")
    attempt_id, attempt = _find_attempt(state, args.round)
    round_worktree = Path(str(attempt["worktree"])).resolve()
    target_files = _target_files_for_state(state)
    manual = Path(args.manual_file).expanduser().resolve() if args.manual_file else (round_worktree / target_files["proof_manual_file"])
    group_plan = (
        Path(args.group_plan).expanduser().resolve()
        if args.group_plan
        else Path(str(attempt["report_directory"])) / "group_plan.json"
    )
    source_goal_version = state.get("source_goal_version")
    if isinstance(source_goal_version, dict):
        source_goal_version = str(source_goal_version.get("digest"))
    if not source_goal_version:
        raise SystemExit("vc-checking-check-round requires current source_goal_version")
    plan = _verify_group_plan(manual, group_plan, str(source_goal_version))
    report_path = Path(str(attempt["report"])).resolve()
    report = _json_load(report_path, {})
    report["kind"] = "vc-checking"
    report["status"] = "accepted"
    report["terminal"] = "yes"
    report["blockers"] = []
    report.setdefault("verification_result", {})["vc_checking_check_round"] = {
        "status": "passed",
        "accepted_at": _utc(),
        "source_version": state.get("source_version"),
        "source_goal_version": state.get("source_goal_version"),
        "group_plan": str(group_plan),
        "target_witnesses": plan.get("target_witnesses", []),
    }
    write_json(report_path, report)
    state.setdefault("accepted_rounds", {})["vc-checking"] = _round_acceptance_payload(
        "vc-checking",
        str(attempt["round"]),
        attempt,
        source_version=state["source_version"],
        source_goal_version=state.get("source_goal_version"),
        extra={"group_plan": str(group_plan)},
    )
    _stale_downstream_acceptance(
        state,
        from_phase="vc-checking",
        reason="accepted vc-checking round replaced proof plan",
    )
    attempt["status"] = "accepted"
    state["phase"] = VC_PROVING_PREPARING_PHASE
    state["current_blockers"] = []
    state["next_actions"] = []
    _append_event(
        run_root,
        state,
        "round-accepted",
        phase="vc-checking",
        round_id=str(attempt["round"]),
        attempt_id=attempt_id,
        details={
            "main_owned_action": "vc-checking-check-round",
            "report": str(report_path),
            "group_plan": str(group_plan),
        },
    )
    _append_phase_transition_timing(
        run_root,
        state,
        previous_phase=previous_phase,
        next_phase=str(state.get("phase") or ""),
    )
    _save_state(run_root, state)
    print(json.dumps({"status": "accepted", "round": attempt["round"], "group_plan": str(group_plan)}, indent=2))
    return 0


def vc_proving_preparing(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    attempt_id, attempt = _find_attempt(state, args.round)
    action = _main_owned_action("vc-proving-preparing", round_id=str(attempt["round"]), attempt=attempt)
    action_errors = _action_validity_errors(state, action)
    if action_errors:
        legacy_action = _main_owned_action("vc-proving-setup", round_id=str(attempt["round"]), attempt=attempt)
        legacy_errors = _action_validity_errors(state, legacy_action)
        if legacy_errors:
            raise SystemExit("vc-proving-preparing action is stale: " + "; ".join(action_errors))
    accepted_vc_checking = state.get("accepted_rounds", {}).get("vc-checking")
    commands: list[dict[str, Any]] = []
    if not isinstance(accepted_vc_checking, dict) or not accepted_vc_checking.get("group_plan"):
        raise SystemExit(
            "vc-proving-preparing requires accepted vc-checking group_plan; "
            "accepted vc-checking round does not expose a controller-verified group_plan"
        )
    source_goal = _current_source_goal_digest(state)
    if not source_goal:
        raise SystemExit("vc-proving-preparing requires current source_goal_version")
    round_worktree = Path(str(attempt["worktree"])).resolve()
    report_dir = Path(str(attempt["report_directory"])).resolve()
    container_dir = Path(str(attempt["container_directory"])).resolve()
    target_files = _target_files_for_state(state)
    group_plan = Path(str(accepted_vc_checking["group_plan"])).expanduser().resolve()
    if not group_plan.is_file():
        raise SystemExit(f"vc-proving-preparing group_plan is missing: {group_plan}")
    helper_root = main_root / ".agents" / "skills" / "vc-proving" / "scripts"
    init_script = helper_root / "init_vc_proving_round.py"
    prepare_script = helper_root / "prepare_group_worktrees.py"
    manifest_path = report_dir / "group_workers_manifest.json"
    init_argv = [
        "python3",
        str(init_script),
        str(round_worktree / target_files["proof_manual_file"]),
        "--case-lib",
        str(round_worktree / target_files["case_lib"]),
        "--source-goal-version",
        source_goal,
        "--round-work-dir",
        str(report_dir),
        "--vc-proving-round-id",
        str(attempt["round"]),
    ]
    prepare_argv = [
        "python3",
        str(prepare_script),
        str(manifest_path),
        "--group-plan",
        str(group_plan),
        "--group-worktree-root",
        str(container_dir),
        "--max-compact-attempts",
        str(int(state.get("max_compact_attempts", 3))),
    ]
    for argv in (init_argv, prepare_argv):
        proc = subprocess.run(
            argv,
            cwd=main_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        evidence = {
            "argv": argv,
            "cwd": str(main_root),
            "returncode": proc.returncode,
            "stdout_tail": proc.stdout[-4000:],
            "stderr_tail": proc.stderr[-4000:],
        }
        commands.append(evidence)
        if proc.returncode != 0:
            raise SystemExit(
                "vc-proving-preparing command failed: "
                + json.dumps(evidence, ensure_ascii=True, sort_keys=True)
            )
    manifest = _json_load(manifest_path, {})
    manifest_errors = _manifest_current_errors(state, attempt, manifest_path, manifest if isinstance(manifest, dict) else {})
    groups = _manifest_groups(manifest) if isinstance(manifest, dict) else []
    if not isinstance(manifest, dict) or manifest_errors or not groups:
        raise SystemExit(
            "vc-proving-preparing did not produce a current non-empty group_workers_manifest.json: "
            + json.dumps(
                {
                    "manifest": str(manifest_path),
                    "errors": manifest_errors or ["manifest has no groups"],
                },
                ensure_ascii=True,
                sort_keys=True,
            )
        )
    attempt["status"] = "ready-for-groups"
    attempt["prepared_at"] = _utc()
    attempt["group_workers_manifest"] = str(manifest_path)
    attempt["group_count"] = len(groups)
    attempt["group_ids"] = [str(group.get("group_id")) for group in groups]
    attempt["preparing_commands"] = commands
    state["current_blockers"] = []
    state["next_actions"] = [
        action
        for action in state.get("next_actions", [])
        if not (
            isinstance(action, dict)
            and action.get("kind") == "main-owned-action"
            and action.get("action") in {"vc-proving-preparing", "vc-proving-setup"}
            and action.get("attempt_id") == attempt_id
        )
    ]
    _sync_vc_proving_next_actions(state, attempt)
    _append_event(
        run_root,
        state,
        "vc-proving-preparing-completed",
        phase=VC_PROVING_PREPARING_PHASE,
        round_id=str(attempt["round"]),
        attempt_id=attempt_id,
        details={"manifest": str(manifest_path), "group_count": len(groups)},
    )
    _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "preparing-completed",
                "round": attempt["round"],
                "container_directory": str(container_dir),
                "manifest": str(manifest_path),
                "group_count": len(groups),
            },
            indent=2,
        )
    )
    return 0


def vc_proving_setup(args: argparse.Namespace) -> int:
    return vc_proving_preparing(args)


def vc_proving_verify(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous_phase = str(state.get("phase") or "")
    attempt_id, attempt = _find_attempt(state, args.round)
    round_worktree = Path(str(attempt["worktree"])).resolve()
    report_dir = Path(str(attempt["report_directory"])).resolve()
    result_path = Path(str(attempt.get("group_merged_result") or (report_dir / "group_merged_result.json"))).resolve()
    result_payload = _json_load(result_path, {}) if result_path.is_file() else {}
    vc = result_payload.get("agent_result", {}).get("vc_proving", {}) if isinstance(result_payload.get("agent_result"), dict) else {}
    merged = result_payload.get("group_merged_result") if isinstance(result_payload.get("group_merged_result"), dict) else {}
    if not isinstance(merged, dict):
        merged = vc.get("group_merged_result") if isinstance(vc, dict) else {}
    parent_verify_command: dict[str, Any] | None = None
    if not isinstance(merged, dict) or merged.get("merge_vc_ready") != "yes":
        manifest_path = report_dir / "group_workers_manifest.json"
        if not manifest_path.is_file():
            raise SystemExit(f"vc-proving-verify requires group_workers_manifest.json: {manifest_path}")
        manifest = _json_load(manifest_path, {})
        current_source_goal = state.get("source_goal_version")
        if isinstance(current_source_goal, dict):
            current_source_goal = current_source_goal.get("digest")
        if manifest.get("source_goal_version") != current_source_goal:
            raise SystemExit("vc-proving-verify source_goal_version is stale")
        manifest_errors = _manifest_current_errors(state, attempt, manifest_path, manifest)
        if manifest_errors:
            raise SystemExit("vc-proving-verify manifest is stale: " + "; ".join(manifest_errors))
        groups = manifest.get("groups") if isinstance(manifest.get("groups"), list) else []
        accepted_groups = _accepted_group_ids(
            state,
            round_id=str(attempt.get("round")),
            source_goal_version=str(current_source_goal),
            manifest_path=manifest_path,
        )
        missing = [str(group.get("group_id")) for group in groups if isinstance(group, dict) and str(group.get("group_id")) not in accepted_groups]
        if missing:
            raise SystemExit("vc-proving-verify requires accepted group reports: " + ", ".join(missing))
        helper = main_root / ".agents" / "skills" / "vc-proving" / "scripts" / "verify_group_results.py"
        argv = ["python3", str(helper), str(manifest_path), "--main-workspace-root", str(main_root)]
        proc = subprocess.run(
            argv,
            cwd=main_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        command_evidence = {
            "argv": argv,
            "cwd": str(main_root),
            "returncode": proc.returncode,
            "stdout_tail": proc.stdout[-4000:],
            "stderr_tail": proc.stderr[-4000:],
        }
        parent_verify_command = command_evidence
        result_payload = _json_load(result_path, {}) if result_path.is_file() else {}
        vc = result_payload.get("agent_result", {}).get("vc_proving", {}) if isinstance(result_payload.get("agent_result"), dict) else {}
        merged = result_payload.get("group_merged_result") if isinstance(result_payload.get("group_merged_result"), dict) else {}
        if not isinstance(merged, dict):
            merged = vc.get("group_merged_result") if isinstance(vc, dict) else {}
        if proc.returncode != 0 or not isinstance(merged, dict) or merged.get("merge_vc_ready") != "yes":
            blockers = merged.get("blockers", []) if isinstance(merged, dict) and isinstance(merged.get("blockers"), list) else []
            errors = merged.get("errors", []) if isinstance(merged, dict) and isinstance(merged.get("errors"), list) else []
            _append_event(
                run_root,
                state,
                "vc-proving-verify-failed",
                phase=VC_PROVING_PREPARING_PHASE,
                round_id=str(attempt["round"]),
                attempt_id=attempt_id,
                details=command_evidence,
            )
            _save_state(run_root, state)
            raise SystemExit(
                "vc-proving-verify failed; main agent decision required: "
                + json.dumps(
                    {
                        "round": attempt["round"],
                        "group_merged_result": str(result_path),
                        "errors": errors or [proc.stderr[-4000:] or proc.stdout[-4000:] or "parent verify failed"],
                        "blockers": blockers,
                    },
                    ensure_ascii=True,
                    sort_keys=True,
                )
            )
    target_files = _target_files_for_state(state)
    attempt["verification_result"] = {
        "status": "passed",
        "accepted_at": _utc(),
        "source_version": state.get("source_version"),
        "source_goal_version": state.get("source_goal_version"),
        "solved_witnesses": merged.get("solved_witnesses", []),
        "parent_verify_command": parent_verify_command
        if parent_verify_command is not None
        else {"status": "skipped", "reason": "ready group_merged_result already existed"},
    }
    state.setdefault("accepted_rounds", {})[VC_PROVING_PREPARING_PHASE] = _round_acceptance_payload(
        VC_PROVING_PREPARING_PHASE,
        str(attempt["round"]),
        attempt,
        source_version=state["source_version"],
        source_goal_version=state.get("source_goal_version"),
        extra={
            "solved_witnesses": merged.get("solved_witnesses", []),
            "group_merged_result": str(result_path),
            "container_directory": attempt.get("container_directory"),
        },
    )
    state["final_candidate"] = {
        "round": str(attempt["round"]),
        "worktree": str(round_worktree),
        "files": [
            {"source": str(round_worktree / target_files[key]), "target": target_files[key]}
            for key in (
                "c_file",
                "case_lib",
                "goal_file",
                "proof_auto_file",
                "proof_manual_file",
                "goal_check_file",
                "proof_diagnostics_file",
                "diagnostics_snapshot",
            )
        ],
    }
    attempt["status"] = "accepted"
    state["phase"] = "final-check"
    state["current_blockers"] = []
    state["next_actions"] = [
        {
            "id": f"final-candidate-apply-{attempt['round']}",
            "kind": "main-owned-action",
            "action": "final-candidate-apply",
            "phase": "final-check",
            "round": str(attempt["round"]),
        }
    ]
    _append_event(
        run_root,
        state,
        "round-accepted",
        phase=VC_PROVING_PREPARING_PHASE,
        round_id=str(attempt["round"]),
        attempt_id=attempt_id,
        details={
            "main_owned_action": "vc-proving-verify",
            "group_merged_result": str(result_path),
            "solved_witness_count": len(merged.get("solved_witnesses", [])),
        },
    )
    _append_phase_transition_timing(
        run_root,
        state,
        previous_phase=previous_phase,
        next_phase=str(state.get("phase") or ""),
    )
    _save_state(run_root, state)
    print(json.dumps({"status": "accepted", "round": attempt["round"]}, indent=2))
    return 0


def annotation_preflight(args: argparse.Namespace) -> int:
    qcp = _json_load(Path(args.qcp_evidence), {}) if args.qcp_evidence else {}
    coq = _json_load(Path(args.coq_evidence), {}) if args.coq_evidence else {}
    errors: list[str] = []
    include_args = qcp.get("include_args") or qcp.get("-I") or qcp.get("I") or []
    slp_args = qcp.get("slp_args") or qcp.get("-slp") or qcp.get("slp") or []
    if CANONICAL_INCLUDE not in include_args:
        errors.append(f"missing canonical -I {CANONICAL_INCLUDE}")
    if list(slp_args) != CANONICAL_SLP:
        errors.append("missing canonical -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM")
    if not qcp.get("driver") or not qcp.get("cwd"):
        errors.append("canonical_symexec_evidence must record driver and cwd")
    if not isinstance(coq, dict) or not coq:
        errors.append("coq evidence is required")
    elif coq.get("target_kind") != "check":
        errors.append("coq evidence must record target_kind check")
    result = {
        "schema_version": "qcp-annotation-preflight/v1",
        "status": "passed" if not errors else "failed",
        "qcp_evidence": qcp,
        "coq_evidence": coq,
        "errors": errors,
        "ready_for_annotation_check_round": not errors,
    }
    if args.output:
        write_json(Path(args.output), result)
    print(json.dumps(result, indent=2, ensure_ascii=True))
    return 0 if not errors else 1


def final_apply(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous_phase = str(state.get("phase") or "")
    candidate = state.get("final_candidate") if isinstance(state.get("final_candidate"), dict) else {}
    files = candidate.get("files") if isinstance(candidate.get("files"), list) else []
    if not files:
        raise SystemExit("run state has no final_candidate.files")
    accepted_rounds = state.get("accepted_rounds") if isinstance(state.get("accepted_rounds"), dict) else {}
    accepted_vc = accepted_rounds.get(VC_PROVING_PREPARING_PHASE)
    if not isinstance(accepted_vc, dict):
        accepted_vc = accepted_rounds.get(VC_PROVING_LEGACY_PHASE)
    if not isinstance(accepted_vc, dict) or not accepted_vc.get("worktree"):
        raise SystemExit("final-apply requires an accepted vc-proving-preparing round")
    accepted_worktree = Path(str(accepted_vc["worktree"])).resolve()
    if str(candidate.get("round")) != str(accepted_vc.get("round")):
        raise SystemExit("final candidate round does not match accepted vc-proving-preparing round")
    if candidate.get("worktree") and Path(str(candidate["worktree"])).resolve() != accepted_worktree:
        raise SystemExit("final candidate worktree does not match accepted vc-proving-preparing worktree")
    report_root = Path(str(state["report_root"]))
    backup_root = report_root / "final-check" / "backup"
    backup_root.mkdir(parents=True, exist_ok=True)
    backup_records: list[dict[str, Any]] = []
    copied_records: list[dict[str, Any]] = []
    copied_targets: list[Path] = []
    try:
        for item in files:
            target_rel = str(item["target"])
            src = Path(str(item["source"])).expanduser().resolve()
            dest = Path(str(state["main_worktree"])) / target_rel
            try:
                src.relative_to(accepted_worktree)
            except ValueError as exc:
                raise RuntimeError(f"candidate source is outside accepted vc-proving-preparing worktree: {src}") from exc
            if not src.is_file():
                raise RuntimeError(f"candidate source file missing: {src}")
            backup_path = backup_root / target_rel
            existed = dest.is_file()
            record = {
                "relative_path": target_rel,
                "existed": existed,
                "backup_path": str(backup_path),
                "sha256_before": _file_digest(dest) if existed else None,
            }
            if existed:
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(dest, backup_path)
            backup_records.append(record)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dest)
            copied_targets.append(dest)
            copied_records.append(
                {
                    "relative_path": target_rel,
                    "source": str(src),
                    "target": str(dest),
                    "source_sha256": _file_digest(src),
                    "sha256_after": _file_digest(dest),
                }
            )
    except Exception as exc:
        rollback = _rollback_final_apply(Path(str(state["main_worktree"])), backup_records, copied_targets)
        state["final_apply"] = {
            "status": "rolled-back",
            "failed_at": _utc(),
            "error": str(exc),
            "backup": backup_records,
            "rollback": rollback,
        }
        state["current_blockers"] = [{"failure_class": "final-apply-failed", "message": str(exc)}]
        _append_event(run_root, state, "final-candidate-apply-blocked", phase="final-check", details=state["final_apply"])
        _save_state(run_root, state)
        raise SystemExit(f"final-apply failed and rollback was attempted: {exc}") from exc
    metadata = {
        "status": "applied",
        "applied_at": _utc(),
        "accepted_round": accepted_vc,
        "backup": backup_records,
        "copied_files": copied_records,
    }
    write_json(report_root / "final-check" / "backup" / "metadata.json", metadata)
    state["final_apply"] = metadata
    _append_event(run_root, state, "final-candidate-applied", phase="final-check", details=metadata)
    state["phase"] = "final-check"
    state["next_actions"] = [
        {
            "id": "final-check",
            "kind": "main-owned-action",
            "action": "final-check",
            "phase": "final-check",
        }
    ]
    _append_phase_transition_timing(
        run_root,
        state,
        previous_phase=previous_phase,
        next_phase=str(state.get("phase") or ""),
    )
    _save_state(run_root, state)
    print(json.dumps({"status": "applied", "files": copied_records}, indent=2))
    return 0


def _rollback_final_apply(main_root: Path, backup_records: list[dict[str, Any]], copied_targets: list[Path] | None = None) -> dict[str, Any]:
    restored: list[dict[str, Any]] = []
    errors: list[str] = []
    copied_set = {path.resolve() for path in copied_targets or []}
    for record in reversed(backup_records):
        rel = str(record.get("relative_path"))
        target = main_root / rel
        try:
            if record.get("existed"):
                backup = Path(str(record.get("backup_path")))
                if not backup.is_file():
                    raise RuntimeError(f"backup missing for {rel}: {backup}")
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(backup, target)
                restored.append({"relative_path": rel, "action": "restored", "sha256_after": _file_digest(target)})
            elif target.resolve() in copied_set and target.exists():
                target.unlink()
                restored.append({"relative_path": rel, "action": "removed-new-file"})
            else:
                restored.append({"relative_path": rel, "action": "not-present"})
        except Exception as exc:
            errors.append(f"{rel}: {exc}")
    return {"status": "passed" if not errors else "failed", "restored": restored, "errors": errors}


def _scan_text_patterns(path: Path, patterns: list[tuple[str, str]]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    if not path.is_file():
        findings.append({"path": str(path), "kind": "missing-file"})
        return findings
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        for kind, pattern in patterns:
            if re.search(pattern, line):
                findings.append({"path": str(path), "line": line_number, "kind": kind, "text": line.strip()[:240]})
    return findings


def _manual_structure_findings(manual_path: Path, expected_witnesses: list[str]) -> list[dict[str, Any]]:
    findings = _scan_text_patterns(
        manual_path,
        [
            ("admitted", r"\bAdmitted\."),
            ("abort", r"\bAbort\."),
            ("extra-axiom", r"^\s*Axiom\b"),
            ("forbidden-top-level", r"^\s*(Definition|Fixpoint|Inductive|Notation)\b"),
        ],
    )
    if not manual_path.is_file():
        return findings
    try:
        _prelude, lemmas = parse_manual_file(manual_path.read_text(encoding="utf-8"))
        ensure_unique_lemma_names(lemmas)
    except Exception as exc:
        findings.append({"path": str(manual_path), "kind": "manual-parse-failed", "message": str(exc)})
        return findings
    expected = set(expected_witnesses)
    actual = [str(lemma["name"]) for lemma in lemmas]
    unexpected = sorted(set(actual) - expected)
    missing = sorted(expected - set(actual))
    for name in unexpected:
        findings.append({"path": str(manual_path), "kind": "unexpected-manual-lemma", "name": name})
    for name in missing:
        findings.append({"path": str(manual_path), "kind": "missing-manual-witness", "name": name})
    return findings


def _manual_witness_evidence(manual_path: Path, source_goal_version: dict[str, Any] | None) -> dict[str, Any]:
    expected_witnesses = []
    expected_hashes = {}
    if isinstance(source_goal_version, dict):
        expected_witnesses = [str(item) for item in source_goal_version.get("target_witnesses", [])]
        expected_hashes = (
            source_goal_version.get("witness_statement_hashes")
            if isinstance(source_goal_version.get("witness_statement_hashes"), dict)
            else {}
        )
    if not manual_path.is_file():
        return {"status": "failed", "errors": [f"manual file missing: {manual_path}"]}
    try:
        _prelude, lemmas = parse_manual_file(manual_path.read_text(encoding="utf-8"))
        ensure_unique_lemma_names(lemmas)
    except Exception as exc:
        return {"status": "failed", "errors": [str(exc)]}
    actual_hashes = {str(lemma["name"]): lemma_statement_hash(lemma) for lemma in lemmas}
    actual_witnesses = [str(lemma["name"]) for lemma in lemmas]
    errors: list[str] = []
    if expected_witnesses and actual_witnesses != expected_witnesses:
        errors.append("manual witness list differs from source_goal_version")
    for name, expected_hash in expected_hashes.items():
        if actual_hashes.get(str(name)) != expected_hash:
            errors.append(f"manual witness statement hash mismatch: {name}")
    return {
        "status": "passed" if not errors else "failed",
        "expected_witnesses": expected_witnesses,
        "actual_witnesses": actual_witnesses,
        "actual_statement_hashes": actual_hashes,
        "errors": errors,
    }


def _case_lib_findings(case_lib_path: Path, active_case_theory: str) -> list[dict[str, Any]]:
    patterns = [
        ("admitted", r"\bAdmitted\."),
        ("extra-axiom", r"^\s*Axiom\b"),
    ]
    findings = _scan_text_patterns(case_lib_path, patterns)
    if not case_lib_path.is_file():
        return findings
    for line_number, line in enumerate(case_lib_path.read_text(encoding="utf-8").splitlines(), start=1):
        if "SimpleC.EE." in line and active_case_theory in line:
            findings.append(
                {
                    "path": str(case_lib_path),
                    "line": line_number,
                    "kind": "generated-artifact-import",
                    "text": line.strip()[:240],
                }
            )
    return findings


def _forbidden_names(main_root: Path) -> list[str]:
    path = main_root / ".agents" / "skills" / "verification-orchestrator" / "docs" / "forbidden-lemma.md"
    if not path.is_file():
        return [
            "functional_extensionality",
            "proof_irrelevance",
            "classic",
            "excluded_middle",
            "derivable1_sepcon_mono",
        ]
    names = set(re.findall(r"`([A-Za-z_][A-Za-z0-9_']*)`", path.read_text(encoding="utf-8")))
    return sorted(names)


def _forbidden_findings(main_root: Path, paths: list[Path]) -> list[dict[str, Any]]:
    names = _forbidden_names(main_root)
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for name in names:
                if name in line:
                    findings.append({"path": str(path), "line": line_number, "kind": "forbidden-lemma", "name": name})
    return findings


def _cleanup_findings(formal_dir: Path) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    if not formal_dir.is_dir():
        return findings
    for path in formal_dir.rglob("*"):
        if not path.is_file():
            continue
        name = path.name
        if name.endswith((".tmp", ".aux")) or "scratch" in name:
            findings.append({"path": str(path), "kind": "cleanup-artifact"})
    return findings


def _final_symexec_refresh_evidence(state: dict[str, Any], main_root: Path, run_root: Path, target_files: dict[str, str]) -> dict[str, Any]:
    refresh_root = Path(str(state["report_root"])) / "final-check" / "symexec-refresh"
    refresh_root.mkdir(parents=True, exist_ok=True)
    driver = main_root / "linux-binary" / "symexec"
    evidence = {
        "schema_version": "qcp-final-symexec-refresh/v1",
        "status": "skipped",
        "refresh_root": str(refresh_root),
        "driver": str(driver),
        "reason": "canonical symexec driver not found or not executable",
    }
    if not driver.is_file() or not driver.stat().st_mode & 0o111:
        return evidence
    # The refresh workspace must not overwrite the proved manual in main worktree.
    # A full isolated replay is case-environment-specific, so the controller records
    # the strict output location and requires generated-file comparison evidence from
    # future symexec integrations instead of running the driver in-place.
    evidence["reason"] = "strict isolated symexec refresh is not configured for this repository layout"
    return evidence


def _final_coq_check(state: dict[str, Any], main_root: Path, run_root: Path, target_files: dict[str, str]) -> dict[str, Any]:
    helper = main_root / ".agents" / "skills" / "vc-proving" / "scripts" / "coq_tooling.py"
    source_goal = state.get("source_goal_version")
    source_goal_digest = source_goal.get("digest") if isinstance(source_goal, dict) else str(source_goal or "")
    if not helper.is_file():
        return {"status": "skipped", "reason": "coq_tooling.py not found", "helper": str(helper)}
    argv = [
        "python3",
        str(helper),
        "check",
        "--workspace-root",
        str(main_root),
        "--build-workspace",
        str(run_builds_root(run_root) / "final-check" / "src"),
        "--target-file",
        target_files["goal_check_file"],
        "--target-kind",
        "check",
        "--source-goal-version",
        source_goal_digest,
    ]
    proc = subprocess.run(
        argv,
        cwd=main_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    return {
        "status": "passed" if proc.returncode == 0 else "failed",
        "argv": argv,
        "cwd": str(main_root),
        "returncode": proc.returncode,
        "stdout_tail": proc.stdout[-4000:],
        "stderr_tail": proc.stderr[-4000:],
        "target_file": target_files["goal_check_file"],
        "target_kind": "check",
        "fixed_flags_hash": fixed_flags_hash(),
        "source_goal_version": source_goal_digest,
    }


def final_check(args: argparse.Namespace) -> int:
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    previous_phase = str(state.get("phase") or "")
    blockers = list(state.get("current_blockers", []))
    if state.get("phase") != "final-check":
        blockers.append({"failure_class": "wrong-phase", "phase": state.get("phase")})
    target_files = _target_files_for_state(state)
    manual_path = main_root / target_files["proof_manual_file"]
    case_lib_path = main_root / target_files["case_lib"]
    expected_witnesses = []
    if isinstance(state.get("source_goal_version"), dict):
        expected_witnesses = [str(item) for item in state["source_goal_version"].get("target_witnesses", [])]
    evidence = {
        "checked_at": _utc(),
        "symexec_refresh": _final_symexec_refresh_evidence(state, main_root, run_root, target_files),
        "manual_witnesses": _manual_witness_evidence(manual_path, state.get("source_goal_version")),
        "coqc_check": {},
        "manual_structure": {},
        "case_lib_contract": {},
        "forbidden-lemma-scan": {},
        "cleanup_scan": {},
    }
    manual_findings = _manual_structure_findings(manual_path, expected_witnesses)
    case_lib_findings = _case_lib_findings(case_lib_path, target_files["active_case_theory"])
    forbidden_findings = _forbidden_findings(main_root, [manual_path, case_lib_path])
    cleanup = _cleanup_findings(main_root / target_files["formal_directory"])
    coq_check = _final_coq_check(state, main_root, run_root, target_files)
    evidence["coqc_check"] = coq_check
    evidence["manual_structure"] = {
        "status": "passed" if not manual_findings else "failed",
        "findings": manual_findings,
    }
    evidence["case_lib_contract"] = {
        "status": "passed" if not case_lib_findings else "failed",
        "findings": case_lib_findings,
    }
    evidence["forbidden-lemma-scan"] = {
        "status": "passed" if not forbidden_findings else "failed",
        "findings": forbidden_findings,
    }
    evidence["cleanup_scan"] = {
        "status": "passed" if not cleanup else "failed",
        "findings": cleanup,
    }
    if evidence["manual_witnesses"].get("status") != "passed":
        blockers.append({"failure_class": "manual-witness-mismatch", "errors": evidence["manual_witnesses"].get("errors", [])})
    if coq_check.get("status") == "failed":
        blockers.append({"failure_class": "final-coqc-check-failed", "evidence": coq_check})
    if manual_findings:
        blockers.append({"failure_class": "manual-structure-failed", "findings": manual_findings})
    if case_lib_findings:
        blockers.append({"failure_class": "case-lib-contract-failed", "findings": case_lib_findings})
    if forbidden_findings:
        blockers.append({"failure_class": "forbidden-lemma-used", "findings": forbidden_findings})
    if cleanup:
        blockers.append({"failure_class": "cleanup-scan-failed", "findings": cleanup})
    status = "passed" if not blockers else "blocked"
    rollback_evidence = None
    if status == "blocked" and isinstance(state.get("final_apply"), dict):
        final_apply_payload = state["final_apply"]
        if final_apply_payload.get("status") == "applied":
            backup_records = (
                final_apply_payload.get("backup")
                if isinstance(final_apply_payload.get("backup"), list)
                else []
            )
            copied_targets = [
                Path(str(item["target"]))
                for item in final_apply_payload.get("copied_files", [])
                if isinstance(item, dict) and item.get("target")
            ]
            rollback_evidence = _rollback_final_apply(main_root, backup_records, copied_targets)
            final_apply_payload["status"] = "rolled-back"
            final_apply_payload["rollback"] = rollback_evidence
    evidence["rollback"] = rollback_evidence
    if status == "passed":
        state["phase"] = "done"
    state["current_blockers"] = blockers
    state["next_actions"] = []
    state["final_check"] = {"status": status, "evidence": evidence}
    _append_event(run_root, state, "final-check-" + status, phase="final-check", details={"blockers": blockers})
    _append_phase_transition_timing(
        run_root,
        state,
        previous_phase=previous_phase,
        next_phase=str(state.get("phase") or ""),
    )
    _save_state(run_root, state)
    print(json.dumps({"status": status, "blockers": blockers, "evidence": evidence}, indent=2))
    return 0 if status == "passed" else 1


def _artifact_error(message: str) -> str:
    return message


def validate_artifact_payload(kind: str, payload: Any, *, path: Path | None = None) -> list[str]:
    errors: list[str] = []
    if kind == "run-log":
        if path is None:
            return [_artifact_error("run-log validation requires --path")]
        if not path.is_file():
            return [_artifact_error(f"missing run log: {path}")]
        for line_number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if not raw_line.strip():
                continue
            try:
                record = json.loads(raw_line)
            except json.JSONDecodeError as exc:
                errors.append(f"line {line_number}: invalid JSON: {exc}")
                continue
            if not isinstance(record, dict):
                errors.append(f"line {line_number}: record must be an object")
                continue
            if record.get("schema_version") != SCHEMA_RUN_LOG:
                errors.append(f"line {line_number}: schema_version must be {SCHEMA_RUN_LOG}")
            if record.get("record_kind") not in {"event", "state_snapshot"}:
                errors.append(f"line {line_number}: record_kind must be event or state_snapshot")
            if not record.get("timestamp"):
                errors.append(f"line {line_number}: timestamp is required")
            if record.get("record_kind") == "state_snapshot" and not isinstance(record.get("state"), dict):
                errors.append(f"line {line_number}: state_snapshot requires state object")
        return errors
    if not isinstance(payload, dict):
        return [_artifact_error("artifact must be a JSON object")]
    if kind == "agent-input":
        if payload.get("schema_version") != "qcp-agent-input/v1":
            errors.append("schema_version must be qcp-agent-input/v1")
        if not isinstance(payload.get("attempt_control"), dict):
            errors.append("attempt_control object is required")
        reports = payload.get("reports")
        if not isinstance(reports, dict):
            errors.append("reports object is required")
        else:
            if set(reports) != {"input", "report", "output"}:
                errors.append("reports must contain exactly input, report, output")
        output_contract = payload.get("output_contract")
        if not isinstance(output_contract, dict):
            errors.append("output_contract object is required")
        elif output_contract.get("kind") != "non-authoritative-reuse-note":
            errors.append("output_contract.kind must be non-authoritative-reuse-note")
        if payload.get("startup", {}).get("script_launch_allowed") != "no":
            errors.append("startup.script_launch_allowed must be no")
    elif kind == "agent-report":
        if payload.get("schema_version") != "qcp-agent-report/v1":
            errors.append("schema_version must be qcp-agent-report/v1")
        if payload.get("status") is None:
            errors.append("status is required")
        if not isinstance(payload.get("agent_result"), dict):
            errors.append("agent_result object is required")
    elif kind == "group-worker-input":
        if payload.get("schema_version") != "qcp-group-worker-input/v1":
            errors.append("schema_version must be qcp-group-worker-input/v1")
        if not isinstance(payload.get("attempt_control"), dict):
            errors.append("attempt_control object is required")
        reports = payload.get("reports")
        if not isinstance(reports, dict):
            errors.append("reports object is required")
        else:
            if set(reports) != {"input", "report", "output"}:
                errors.append("reports must contain exactly input, report, output")
        output_contract = payload.get("output_contract")
        if not isinstance(output_contract, dict):
            errors.append("output_contract object is required")
        elif output_contract.get("kind") != "non-authoritative-reuse-note":
            errors.append("output_contract.kind must be non-authoritative-reuse-note")
        namespace = payload.get("helper_namespace")
        if not isinstance(namespace, dict) or namespace.get("policy") != "group-id-suffixed":
            errors.append("helper_namespace policy must be group-id-suffixed")
    elif kind == "group-worker-report":
        if payload.get("schema_version") != "qcp-group-worker-report/v1":
            errors.append("schema_version must be qcp-group-worker-report/v1")
        group = (
            payload.get("agent_result", {}).get("vc_proving", {}).get("group", {})
            if isinstance(payload.get("agent_result"), dict)
            else {}
        )
        if not isinstance(group, dict) or not group:
            errors.append("agent_result.vc_proving.group object is required")
    elif kind == "manifest":
        if payload.get("schema_version") != "qcp-vc-proving-group-workers-manifest/v1":
            errors.append("schema_version must be qcp-vc-proving-group-workers-manifest/v1")
        if not payload.get("source_goal_version"):
            errors.append("source_goal_version is required")
        if not isinstance(payload.get("groups"), list):
            errors.append("groups list is required")
        else:
            for index, group in enumerate(payload["groups"]):
                if not isinstance(group, dict):
                    errors.append(f"groups[{index}] must be an object")
                    continue
                handoff = group.get("handoff_files")
                if handoff is not None and (not isinstance(handoff, dict) or set(handoff) != {"input", "report", "output"}):
                    errors.append(f"groups[{index}].handoff_files must contain exactly input, report, output")
    else:
        errors.append(f"unsupported artifact kind: {kind}")
    return errors


def validate_artifact(args: argparse.Namespace) -> int:
    path = Path(args.path).expanduser().resolve()
    payload: Any = None
    if args.kind != "run-log":
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except FileNotFoundError:
            print(json.dumps({"status": "invalid", "errors": [f"missing artifact: {path}"]}, indent=2))
            return 1
        except json.JSONDecodeError as exc:
            print(json.dumps({"status": "invalid", "errors": [f"invalid JSON: {exc}"]}, indent=2))
            return 1
    errors = validate_artifact_payload(args.kind, payload, path=path)
    status = "valid" if not errors else "invalid"
    print(json.dumps({"status": status, "kind": args.kind, "path": str(path), "errors": errors}, indent=2))
    return 0 if not errors else 1


def _first_phase_result(agent_result: dict[str, Any]) -> tuple[str, dict[str, Any]] | tuple[None, dict[str, Any]]:
    for key in ("annotation", "vc_checking", "vc_proving"):
        value = agent_result.get(key)
        if isinstance(value, dict):
            return key, value
    vc_group = agent_result.get("vc_proving", {}).get("group", {}) if isinstance(agent_result.get("vc_proving"), dict) else {}
    if isinstance(vc_group, dict) and vc_group:
        return "vc_proving.group", vc_group
    return None, {}


def render_output(args: argparse.Namespace) -> int:
    report_path = Path(args.report).expanduser().resolve()
    output_path = Path(args.output).expanduser().resolve()
    report = _json_load(report_path, {})
    if not isinstance(report, dict):
        raise SystemExit(f"invalid report JSON: {report_path}")
    agent_result = report.get("agent_result") if isinstance(report.get("agent_result"), dict) else {}
    phase_key, phase_result = _first_phase_result(agent_result)
    lines = [
        "# Reuse Note",
        "",
        "Note kind: non-authoritative reuse note",
        "",
        "This file is not acceptance evidence. If it conflicts with JSON reports, handoff files, source versions, manifests, or current worktree files, ignore this file.",
        "",
        "Role: deterministic renderer",
        "Round:",
        "Attempt:",
        f"Report: {report_path}",
        "Worktree:",
        "Source version:",
        "Source goal version:",
        "",
        "## Result",
        "",
        f"Owner status: {report.get('status', 'unknown')}",
        "Ready for controller check:",
        "Primary blockers:",
    ]
    if phase_key:
        lines.append(f"Agent result: {phase_key} status {phase_result.get('status', 'unknown')}")
    changed = phase_result.get("changed_files") if isinstance(phase_result.get("changed_files"), list) else []
    lines.extend(["", "## Files Touched", ""])
    if changed:
        lines.extend(f"- {item}" for item in changed)
    else:
        lines.append("- none recorded")
    lines.extend(["", "## Useful Method", "", "- See JSON report evidence fields."])
    lines.extend(["", "## Failed Attempts", ""])
    blockers = report.get("blockers") if isinstance(report.get("blockers"), list) else []
    if not blockers and isinstance(phase_result.get("blockers"), list):
        blockers = phase_result["blockers"]
    if blockers:
        lines.extend(f"- {json.dumps(item, sort_keys=True, ensure_ascii=True)}" for item in blockers)
    else:
        lines.append("- none recorded")
    errors = phase_result.get("errors") if isinstance(phase_result.get("errors"), list) else []
    if errors:
        lines.extend(f"- {json.dumps(item, sort_keys=True, ensure_ascii=True)}" for item in errors)
    verification = report.get("verification_result") if isinstance(report.get("verification_result"), dict) else {}
    lines.extend(["", "## Evidence Pointers", ""])
    if verification:
        lines.extend(f"- verification_result.{key}" for key in sorted(verification))
    else:
        lines.append("- none recorded")
    lines.extend(["", "## Next Attempt Guidance", "", "- Read the JSON report first; use this note only as reusable context."])
    lines.extend(["", "## Caveats", "", "- This renderer does not infer semantic conclusions from chat transcripts."])
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps({"status": "rendered", "output": str(output_path)}, indent=2))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Controller for QCP verification runs.")
    parser.add_argument("--main-worktree-root", default=None)
    sub = parser.add_subparsers(dest="command", required=True)

    init = sub.add_parser("init-run")
    init.add_argument("--case", required=True)
    init.add_argument("--target-c-file", required=True)
    init.add_argument("--timestamp", default=None)
    init.add_argument("--max-compact-attempts", type=int, default=3)
    init.add_argument("--problem-statement", default="")
    init.add_argument("--problem-statement-file", default=None)
    init.add_argument("--target-function", default="")
    init.add_argument("--expected-behavior", default="")
    init.add_argument("--input-output-contract", default="")
    init.add_argument("--spec-hint", action="append", default=[])
    init.add_argument("--preferred-hidden-property", action="append", default=[])
    init.add_argument("--forbidden-pattern", action="append", default=[])
    init.add_argument("--reference-case-hint", action="append", default=[])
    init.add_argument("--reference-policy-mode", choices=["default", "deny-existing-examples"], default="default")
    init.add_argument("--allowed-reference-glob", action="append", default=[])
    init.add_argument("--denied-reference-glob", action="append", default=[])
    init.add_argument("--must-log-file-reads", choices=["yes", "no"], default="yes")
    init.set_defaults(func=init_run)

    step_cmd = sub.add_parser("step")
    step_cmd.add_argument("--run", required=True)
    step_cmd.set_defaults(func=step)

    spawn = sub.add_parser("spawn-instructions")
    spawn.add_argument("--run", required=True)
    spawn.add_argument("--next-action", required=True)
    spawn.set_defaults(func=spawn_instructions)

    started = sub.add_parser("mark-attempt-started")
    started.add_argument("--run", required=True)
    started.add_argument("--attempt", required=True)
    started.set_defaults(func=mark_attempt_started)

    returned = sub.add_parser("mark-attempt-returned")
    returned.add_argument("--run", required=True)
    returned.add_argument("--attempt", required=True)
    returned.add_argument(
        "--result-status",
        choices=["completed", "blocked", "stale", "compact-error", "returned"],
        default="returned",
    )
    returned.set_defaults(func=mark_attempt_returned)

    retry = sub.add_parser("retry-round")
    retry.add_argument("--run", required=True)
    retry.add_argument("--phase", required=True, choices=["annotation", "vc-checking"])
    retry.add_argument("--reason", required=True)
    retry.add_argument("--previous-attempt", required=True)
    retry.set_defaults(func=retry_round)

    review = sub.add_parser("review-attempt")
    review.add_argument("--run", required=True)
    review.add_argument("--attempt", required=True)
    review.add_argument("--run-main-check-if-ready", action="store_true")
    review.set_defaults(func=review_attempt)

    verify = sub.add_parser("verify-round")
    verify.add_argument("--run", required=True)
    verify.add_argument("--round", required=True)
    verify.add_argument("--manual-file", default=None)
    verify.add_argument("--group-plan", default=None)
    verify.add_argument("--source-goal-version", default=None)
    verify.set_defaults(func=verify_round)

    annotation_accept = sub.add_parser("annotation-check-round")
    annotation_accept.add_argument("--run", required=True)
    annotation_accept.add_argument("--round", required=True)
    annotation_accept.set_defaults(func=annotation_check_round)

    vc_checking_accept = sub.add_parser("vc-checking-check-round")
    vc_checking_accept.add_argument("--run", required=True)
    vc_checking_accept.add_argument("--round", required=True)
    vc_checking_accept.add_argument("--manual-file", default=None)
    vc_checking_accept.add_argument("--group-plan", default=None)
    vc_checking_accept.set_defaults(func=vc_checking_check_round)

    vc_proving_prepare_cmd = sub.add_parser("vc-proving-preparing")
    vc_proving_prepare_cmd.add_argument("--run", required=True)
    vc_proving_prepare_cmd.add_argument("--round", required=True)
    vc_proving_prepare_cmd.set_defaults(func=vc_proving_preparing)

    vc_proving_setup_cmd = sub.add_parser("vc-proving-setup")
    vc_proving_setup_cmd.add_argument("--run", required=True)
    vc_proving_setup_cmd.add_argument("--round", required=True)
    vc_proving_setup_cmd.set_defaults(func=vc_proving_setup)

    vc_proving_accept = sub.add_parser("vc-proving-verify")
    vc_proving_accept.add_argument("--run", required=True)
    vc_proving_accept.add_argument("--round", required=True)
    vc_proving_accept.set_defaults(func=vc_proving_verify)

    preflight = sub.add_parser("annotation-preflight")
    preflight.add_argument("--qcp-evidence", required=True)
    preflight.add_argument("--coq-evidence", required=True)
    preflight.add_argument("--output", default=None)
    preflight.set_defaults(func=annotation_preflight)

    apply_cmd = sub.add_parser("final-apply")
    apply_cmd.add_argument("--run", required=True)
    apply_cmd.set_defaults(func=final_apply)

    final = sub.add_parser("final-check")
    final.add_argument("--run", required=True)
    final.set_defaults(func=final_check)

    validate = sub.add_parser("validate-artifact")
    validate.add_argument(
        "--kind",
        required=True,
        choices=[
            "agent-input",
            "agent-report",
            "group-worker-input",
            "group-worker-report",
            "manifest",
            "run-log",
        ],
    )
    validate.add_argument("--path", required=True)
    validate.set_defaults(func=validate_artifact)

    render = sub.add_parser("render-output")
    render.add_argument("--report", required=True)
    render.add_argument("--output", required=True)
    render.set_defaults(func=render_output)

    output_check = sub.add_parser("check-output-note")
    output_check.add_argument("--path", required=True)
    output_check.add_argument("--input", default=None)
    output_check.add_argument("--report", default=None)
    output_check.set_defaults(func=check_output_note)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if getattr(args, "command", None) == "init-run" or not getattr(args, "run", None):
        return int(args.func(args))
    main_root = Path(args.main_worktree_root).expanduser().resolve() if args.main_worktree_root else Path.cwd().resolve()
    run_root: Path | None = None
    state: dict[str, Any] | None = None
    timer_key = f"controller_command:{args.command}"
    try:
        run_root = _run_root_from_id(main_root, args.run)
        state = _load_state(run_root)
        _append_run_timing_node(
            run_root,
            state,
            event="controller-command-start",
            node_type="start",
            category="controller_command",
            name=str(args.command),
            timer_key=timer_key,
        )
    except SystemExit:
        return int(args.func(args))
    try:
        result = int(args.func(args))
    except BaseException:
        if run_root is not None:
            try:
                latest_state = _load_state(run_root)
            except SystemExit:
                latest_state = state
            _append_run_timing_node(
                run_root,
                latest_state,
                event="controller-command-end",
                node_type="end",
                category="controller_command",
                name=str(args.command),
                timer_key=timer_key,
            )
        raise
    if run_root is not None:
        try:
            latest_state = _load_state(run_root)
        except SystemExit:
            latest_state = state
        _append_run_timing_node(
            run_root,
            latest_state,
            event="controller-command-end",
            node_type="end",
            category="controller_command",
            name=str(args.command),
            timer_key=timer_key,
        )
    return result


if __name__ == "__main__":
    raise SystemExit(main())
