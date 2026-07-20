#!/usr/bin/env python3
"""Directory and handoff helpers for the copy/merge verification pipeline.

The module owns deterministic run/report paths and group file copies.  It does
not own controller transitions, proof acceptance, or writes to formal files in
the repository root.
"""

from __future__ import annotations

import json
import re
import shutil
from datetime import datetime
from pathlib import Path
from typing import Any


GROUP_WORKER_FILE_SET = (
    "group_worker_input.md",
    "group_worker_report.json",
    "group_worker_output.md",
)
VERIFICATION_RUNS_DIR_NAME = "verification_runs"
RUN_BUILDS_DIR_NAME = "_coq_builds"
ANNOTATION_HISTORY_DIR_NAME = "annotation_history"
ANNOTATION_ATTEMPTS_DIR_NAME = "annotation-attempts"
ANNOTATION_ATTEMPT_DIR_PREFIX = "annotation-attempt"
REPORTS_DIR_NAME = "reports"
CONTROLLER_STATE_FILE_NAME = "controller_state.json"
RUN_ROOT_RE = re.compile(r"^.+-\d{14}(?:-\d{2})?$")


def group_worker_spawn_message(input_path: Path | str, report_path: Path | str) -> str:
    return (
        f"Read {input_path} completely and follow it as the source of truth. "
        f"Work only on the assigned group, then write the terminal result to {report_path}. "
        "Do not rely on parent transcript; controller acceptance is separate."
    )


def slug(value: object) -> str:
    text = re.sub(r"[^A-Za-z0-9_.-]+", "-", str(value).strip())
    text = text.strip("-._")
    return text or "unnamed"


def coq_identifier_slug(value: object) -> str:
    """Render an arbitrary path/group label as a legal Rocq identifier."""

    text = re.sub(r"[^A-Za-z0-9_]+", "_", str(value).strip())
    text = re.sub(r"_+", "_", text).strip("_")
    if not text:
        return "unnamed"
    if text[0].isdigit():
        return "_" + text
    return text


def relative_to_root(path: Path, root: Path) -> Path | None:
    try:
        return path.expanduser().resolve().relative_to(root.expanduser().resolve())
    except ValueError:
        return None


def target_files_for_c(target_c_relative: str | Path) -> dict[str, str]:
    """Return every formal relative path derived from a repository C path."""

    target_path = Path(str(target_c_relative))
    if target_path.is_absolute() or ".." in target_path.parts:
        raise ValueError(f"target C path must be repository-relative: {target_path}")
    case_name = target_path.stem
    logical_parts = target_path.parts[1:-1] if target_path.parts and target_path.parts[0] == "QCP_examples" else target_path.parts[:-1]
    formal_dir = Path("SeparationLogic") / "examples" / Path(*logical_parts)
    active_case_theory = "SimpleC.EE." + ".".join(logical_parts) if logical_parts else "SimpleC.EE"
    return {
        "c_file": target_path.as_posix(),
        "formal_directory": formal_dir.as_posix(),
        "formal_case_lib": (formal_dir / f"{case_name}_lib.v").as_posix(),
        "goal_file": (formal_dir / f"{case_name}_goal.v").as_posix(),
        "proof_auto_file": (formal_dir / f"{case_name}_proof_auto.v").as_posix(),
        "proof_manual_file": (formal_dir / f"{case_name}_proof_manual.v").as_posix(),
        "goal_check_file": (formal_dir / f"{case_name}_goal_check.v").as_posix(),
        "proof_diagnostics_file": (formal_dir / f"{case_name}_proof_diagnostics.v").as_posix(),
        "diagnostics_snapshot": (formal_dir / "diagnostics_snapshot.json").as_posix(),
        "case_name": case_name,
        "active_case_theory": active_case_theory,
    }


def is_run_root_name(name: str) -> bool:
    return RUN_ROOT_RE.fullmatch(name) is not None


def run_root_from_path(path: Path, main_root: Path) -> Path | None:
    resolved = path.expanduser().resolve()
    main = main_root.expanduser().resolve()
    for owner in (VERIFICATION_RUNS_DIR_NAME, REPORTS_DIR_NAME):
        try:
            rel = resolved.relative_to(main / owner)
        except ValueError:
            continue
        if not rel.parts or not is_run_root_name(rel.parts[0]):
            continue
        return (main / VERIFICATION_RUNS_DIR_NAME / rel.parts[0]).resolve()
    return None


def main_root_from_run_root(run_root: Path) -> Path:
    run_root = run_root.expanduser().resolve()
    if run_root.parent.name != VERIFICATION_RUNS_DIR_NAME:
        raise SystemExit(f"run root must be under <main-root>/{VERIFICATION_RUNS_DIR_NAME}: {run_root}")
    return run_root.parent.parent.resolve()


def ensure_run_root(
    main_root: Path,
    case_name: str,
    *,
    path_hint: Path | None = None,
    timestamp: str | None = None,
) -> Path:
    main_root = main_root.expanduser().resolve()
    if path_hint is not None:
        existing = run_root_from_path(path_hint, main_root)
        if existing is not None:
            (existing / RUN_BUILDS_DIR_NAME).mkdir(parents=True, exist_ok=True)
            (existing / ANNOTATION_HISTORY_DIR_NAME).mkdir(parents=True, exist_ok=True)
            reports_root(existing)
            return existing
    stamp = timestamp or datetime.now().strftime("%Y%m%d%H%M%S")
    base_name = f"{slug(case_name)}-{stamp}"
    parent = main_root / VERIFICATION_RUNS_DIR_NAME
    parent.mkdir(parents=True, exist_ok=True)
    run_root = parent / base_name
    suffix = 1
    while run_root.exists() and any(run_root.iterdir()):
        run_root = parent / f"{base_name}-{suffix:02d}"
        suffix += 1
    run_root.mkdir(parents=True, exist_ok=True)
    (run_root / RUN_BUILDS_DIR_NAME).mkdir(parents=True, exist_ok=True)
    (run_root / ANNOTATION_HISTORY_DIR_NAME).mkdir(parents=True, exist_ok=True)
    reports_root(run_root)
    return run_root.resolve()


def run_builds_root(run_root: Path) -> Path:
    path = run_root.expanduser().resolve() / RUN_BUILDS_DIR_NAME
    path.mkdir(parents=True, exist_ok=True)
    return path


def annotation_history_root(run_root: Path) -> Path:
    path = run_root.expanduser().resolve() / ANNOTATION_HISTORY_DIR_NAME
    path.mkdir(parents=True, exist_ok=True)
    return path


def reports_root(run_root: Path) -> Path:
    run_root = run_root.expanduser().resolve()
    path = main_root_from_run_root(run_root) / REPORTS_DIR_NAME / run_root.name
    path.mkdir(parents=True, exist_ok=True)
    return path


def annotation_attempt_report_root(run_root: Path, attempt_number: int) -> Path:
    """Return the immutable report directory for one persistent-agent iteration."""

    if attempt_number < 1:
        raise ValueError("annotation attempt number must be positive")
    path = reports_root(run_root) / ANNOTATION_ATTEMPTS_DIR_NAME / f"{ANNOTATION_ATTEMPT_DIR_PREFIX}{attempt_number}"
    path.mkdir(parents=True, exist_ok=True)
    return path


def controller_state_path(run_root: Path) -> Path:
    return reports_root(run_root) / CONTROLLER_STATE_FILE_NAME


def run_logs_path(run_root: Path) -> Path:
    return reports_root(run_root) / "run_logs.json"


def round_report_root(run_root: Path, round_id: str) -> Path:
    path = reports_root(run_root) / "rounds" / slug(round_id)
    path.mkdir(parents=True, exist_ok=True)
    return path


def prepare_group_directory(
    *,
    groups_root: Path,
    group_id: str,
    index: int,
    formal_manual: Path,
    formal_case_lib: Path,
    force: bool = False,
) -> tuple[Path, Path, Path]:
    """Create a group directory containing only copied manual/lib formal inputs."""

    groups_root = groups_root.expanduser().resolve()
    groups_root.mkdir(parents=True, exist_ok=True)
    directory = groups_root / f"group_{index:02d}__{slug(group_id)}"
    if directory.exists():
        if not force:
            raise SystemExit(f"group directory already exists: {directory}; pass --force-groups to replace it")
        shutil.rmtree(directory)
    directory.mkdir(parents=True)
    group_manual = directory / formal_manual.name
    group_worker_lib = directory / formal_case_lib.name
    shutil.copy2(formal_manual, group_manual)
    shutil.copy2(formal_case_lib, group_worker_lib)
    return directory.resolve(), group_manual.resolve(), group_worker_lib.resolve()


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(text.rstrip() + "\n", encoding="utf-8")
    temporary.replace(path)


def render_group_worker_input(
    group: dict[str, Any],
    *,
    source_goal_version: str,
    formal_case_lib: str,
    report_dir: Path,
    attempt_index: int = 1,
    previous_compact_attempts: int = 0,
) -> str:
    witnesses = "\n".join(f"- `{name}`" for name in group["witnesses"])
    dependencies = ", ".join(group.get("depends_on", [])) or "none"
    helpers = "\n".join(f"- {item}" for item in group.get("helpers", [])) or "- none planned"
    return f"""# Group worker handoff

Source of truth: this file, the current copied files, and the listed skill docs. Do not use the parent transcript.

## Assignment

- Group: `{group['id']}`
- Attempt: {attempt_index}
- Earlier compact attempts: {previous_compact_attempts}
- `source_goal_version`: `{source_goal_version}`
- Dependencies: {dependencies}
- Helper suffix: `{group['helper_namespace']['suffix']}` (required for every new helper)

Assigned witnesses:

{witnesses}

## Files

- Group directory: `{group['directory']}`
- Copied manual: `{group['proof_manual']}` — edit assigned proof bodies only
- `group_worker_lib`: `{group['group_worker_lib']}` — add proved suffixed helpers and official Rocq imports only
- `formal_case_lib`: `{formal_case_lib}` — read-only
- Terminal report: `{report_dir / 'group_worker_report.json'}`
- Optional human notes: `{report_dir / 'group_worker_output.md'}`

The group directory must finish with only the copied manual and `group_worker_lib`.

## Proof hints

Strategy: {group.get('strategy') or 'derive a proof from the current VC'}

Candidate helpers:

{helpers}

## Commands

Run these exact controller commands; do not reconstruct paths or flags:

```text
{group['debug_command']}
{group['check_command']}
```

Debug script (optional): `{group['debug_script']}`

## Rules

- Read `.agents/skills/group-worker-proving/SKILL.md` and its linked proof/tooling guides.
- Do not edit generated files, unassigned witnesses, witness statements, or `formal_case_lib`.
- Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, extra `Axiom`, or forbidden lemmas.
- Repair recoverable proof failures in this spawn. Use `blocked` only for a concrete semantic/tool blocker; use `stale` for a version mismatch and `compact-error` only for compaction.
- Write the compact JSON report only at the end. `completed` means all assigned witnesses are solved and the exact group check passes; controller will rerun the check before acceptance.
"""


def build_group_worker_report_payload(*, source_goal_version: str) -> dict[str, Any]:
    return {
        "schema_version": "qcp-group-worker-report/v2",
        "status": "pending",
        "source_goal_version": source_goal_version,
        "blockers": [],
    }


def init_group_worker_files(
    *,
    report_dir: Path,
    group: dict[str, Any],
    source_goal_version: str,
    formal_case_lib: str,
) -> None:
    report_dir = report_dir.resolve()
    write_text(
        report_dir / "group_worker_input.md",
        render_group_worker_input(
            group,
            source_goal_version=source_goal_version,
            formal_case_lib=formal_case_lib,
            report_dir=report_dir,
        ),
    )
    write_json(
        report_dir / "group_worker_report.json",
        build_group_worker_report_payload(source_goal_version=source_goal_version),
    )
    write_text(report_dir / "group_worker_output.md", "# Worker notes\n\nOptional concise notes for retries or human review.")
