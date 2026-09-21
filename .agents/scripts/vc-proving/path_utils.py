#!/usr/bin/env python3
"""Directory and handoff helpers for the copy/merge verification pipeline.

The module owns deterministic run/report paths and group file copies.  It does
not own controller transitions, proof acceptance, or writes to formal files in
the repository root.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import stat
import sys
from contextlib import suppress
from datetime import datetime
from pathlib import Path
from typing import Any

from atomic_file import atomic_write_bytes

GROUP_WORKER_FILE_SET = (
    "group_worker_input.md",
    "group_worker_report.json",
)
VERIFICATION_RUNS_DIR_NAME = "verification_runs"
RUN_BUILDS_DIR_NAME = "_coq_builds"
RUN_MAKEFILE_NAME = "Makefile"
ANNOTATION_HISTORY_DIR_NAME = "annotation_history"
ANNOTATION_ATTEMPTS_DIR_NAME = "annotation-attempts"
ANNOTATION_ATTEMPT_DIR_PREFIX = "annotation-attempt"
REPORTS_DIR_NAME = "reports"
CONTROLLER_STATE_FILE_NAME = "controller_state.json"
RUN_ROOT_RE = re.compile(r"^.+-\d{14}(?:-\d{2})?$")
TARGET_FILE_FIELDS = frozenset(
    {
        "c_file",
        "formal_directory",
        "formal_case_lib",
        "goal_file",
        "proof_auto_file",
        "proof_manual_file",
        "goal_check_file",
        "case_name",
        "active_case_theory",
    }
)


def group_worker_spawn_message(input_path: Path | str, report_path: Path | str) -> str:
    return (
        f"Read {input_path} completely and follow it as the source of truth. "
        f"Work only on the assigned group, then write the terminal result to {report_path}. "
        "Do not rely on parent transcript; controller acceptance is separate."
    )


def group_worker_append_message(input_path: Path | str, report_path: Path | str) -> str:
    return (
        f"Continue the same group-worker session and reread {input_path} completely. "
        "Repair the controller failure in the existing fixed group directory, "
        f"then update the terminal result at {report_path}. Do not start a new worker or edit another group."
    )


def group_worker_commands(
    *,
    main_root: Path,
    run_root: Path,
    round_id: str,
    group_id: str,
    group_directory: Path,
) -> dict[str, Any]:
    """Derive current handoff commands from fixed controller-owned paths."""

    controller = Path(__file__).resolve().parents[1] / "verification-orchestrator/controller.py"

    common = [
        sys.executable,
        str(controller),
        "--main-root",
        str(main_root),
    ]
    check = [
        *common,
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
    development = [
        *common,
        "coq-check",
        "--run",
        run_root.name,
        "--round",
        round_id,
        "--target-kind",
        "group-development",
        "--group",
        group_id,
    ]
    debug = [
        *common,
        "coq-debug",
        "--run",
        run_root.name,
        "--round",
        round_id,
        "--group",
        group_id,
    ]
    debug_script = (
        group_build_workspace(run_root, round_id, group_directory.name)
        / ".coq_debug"
        / group_debug_script_name(group_directory.name)
    )
    return {
        "check": {"argv": check, "cwd": str(main_root)},
        "development": {"argv": development, "cwd": str(main_root)},
        "debug": {"argv": debug, "cwd": str(main_root)},
        "debug_script": str(debug_script),
    }


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


def group_debug_script_name(directory_name: object) -> str:
    """Return the one canonical debug-script filename for a group directory."""

    return f"{coq_identifier_slug(directory_name)}.v"


def group_workspace_name(directory_name: object) -> str:
    """Use the controller-owned group index as the short build identity."""

    match = re.fullmatch(r"(group_[0-9]+)__.+", str(directory_name))
    if match is None:
        raise ValueError(f"invalid controller group directory name: {directory_name}")
    return match.group(1)


def group_build_workspace(
    run_root: Path, round_id: str, directory_name: object
) -> Path:
    """Return the shared compact exact workspace for one group directory."""

    return (
        run_root / RUN_BUILDS_DIR_NAME
        / round_id
        / group_workspace_name(directory_name)
        / "src"
    )


def relative_to_root(path: Path, root: Path) -> Path | None:
    try:
        return path.expanduser().resolve().relative_to(root.expanduser().resolve())
    except ValueError:
        return None


def _lexical_absolute(path: Path) -> Path:
    """Normalize ``.``/``..`` without following any filesystem symlink."""

    return Path(os.path.abspath(os.fspath(path.expanduser())))


def path_is_link_like(path: Path) -> bool:
    """Return whether an existing path can redirect traversal.

    ``Path.is_symlink`` is sufficient on POSIX.  On Windows, junctions and
    other reparse points can redirect directory traversal without reporting as
    ordinary symlinks, so the controller rejects those as well.
    """

    if path.is_symlink():
        return True
    is_junction = getattr(path, "is_junction", None)
    if callable(is_junction) and is_junction():
        return True
    try:
        attributes = int(getattr(path.lstat(), "st_file_attributes", 0) or 0)
    except FileNotFoundError:
        return False
    return bool(attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400))


def _reject_symlink_components(path: Path, *, label: str) -> Path:
    """Reject every existing link/reparse component of a lexical path."""

    candidate = path.expanduser()
    if not candidate.is_absolute():
        candidate = Path.cwd() / candidate
    cursor = Path(candidate.anchor)
    # Inspect before collapsing '..': link/../file still traverses the link.
    for part in candidate.parts[1:]:
        cursor /= part
        if path_is_link_like(cursor):
            raise SystemExit(
                f"{label} cannot use a symlink ancestor or reparse point: {cursor}"
            )
    return _lexical_absolute(candidate)


def fixed_path_under(path: Path, root: Path, *, label: str) -> Path:
    """Return a non-symlink lexical path confined to ``root``.

    Destructive callers must use the returned lexical path directly. Resolving
    first would follow a hostile child symlink and turn an in-run cleanup into
    deletion of its external target.
    """

    owner = _reject_symlink_components(root, label=f"{label} owner")
    candidate = path.expanduser()
    if not candidate.is_absolute():
        candidate = owner / candidate
    candidate = _reject_symlink_components(candidate, label=label)
    try:
        candidate.relative_to(owner)
    except ValueError as exc:
        raise SystemExit(
            f"{label} escaped its fixed owner {owner}: {candidate}"
        ) from exc
    return candidate


def target_files_for_c(
    target_c_relative: str | Path,
    formal_case_name: str,
) -> dict[str, str]:
    """Return the canonical formal paths for one repository C target.

    ``formal_case_name`` is the controller-owned Rocq module-family identity.
    It is intentionally independent of the C filename: several C programs may
    share one directory, and a filename such as ``3DGraphField.c`` is not a
    legal Rocq module prefix.  Callers must provide this persisted identity;
    the C stem is not the formal identity.
    """

    target_path = Path(str(target_c_relative))
    if (
        target_path.is_absolute()
        or ".." in target_path.parts
        or target_path.suffix.lower() != ".c"
        or len(target_path.parts) < 3
        or target_path.parts[0] != "QCP_examples"
    ):
        raise ValueError(
            "target C path must be a repository-relative "
            f"QCP_examples/<collection>/.../*.c path: {target_path}"
        )
    if not isinstance(formal_case_name, str):
        raise ValueError("formal case name must be a string")
    resolved_case_name = formal_case_name
    rocq_identifier = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
    if rocq_identifier.fullmatch(resolved_case_name) is None:
        raise ValueError(
            "formal case name must be a legal Rocq module identifier "
            f"(and must not start with a digit): {resolved_case_name!r}"
        )
    logical_parts = target_path.parts[1:-1]
    invalid_directory_parts = [
        part for part in logical_parts if rocq_identifier.fullmatch(part) is None
    ]
    if invalid_directory_parts:
        raise ValueError(
            "target C directory cannot form a Rocq logical path; invalid "
            f"component: {invalid_directory_parts[0]!r}"
        )
    formal_dir = Path("Rocq") / "examples" / Path(*logical_parts)
    active_case_theory = "SimpleC.EE." + ".".join(logical_parts)
    return {
        "c_file": target_path.as_posix(),
        "formal_directory": formal_dir.as_posix(),
        "formal_case_lib": (
            formal_dir / f"{resolved_case_name}_lib.v"
        ).as_posix(),
        "goal_file": (formal_dir / f"{resolved_case_name}_goal.v").as_posix(),
        "proof_auto_file": (
            formal_dir / f"{resolved_case_name}_proof_auto.v"
        ).as_posix(),
        "proof_manual_file": (
            formal_dir / f"{resolved_case_name}_proof_manual.v"
        ).as_posix(),
        "goal_check_file": (
            formal_dir / f"{resolved_case_name}_goal_check.v"
        ).as_posix(),
        "case_name": resolved_case_name,
        "active_case_theory": active_case_theory,
    }


def is_run_root_name(name: str) -> bool:
    return RUN_ROOT_RE.fullmatch(name) is not None


def run_root_from_path(path: Path, main_root: Path) -> Path | None:
    main = _reject_symlink_components(main_root, label="main root")
    resolved = fixed_path_under(path, main, label="run-owned path")
    for owner in (VERIFICATION_RUNS_DIR_NAME, REPORTS_DIR_NAME):
        try:
            rel = resolved.relative_to(main / owner)
        except ValueError:
            continue
        if not rel.parts or not is_run_root_name(rel.parts[0]):
            continue
        return fixed_path_under(
            main / VERIFICATION_RUNS_DIR_NAME / rel.parts[0],
            main,
            label="run root",
        )
    return None


def main_root_from_run_root(run_root: Path) -> Path:
    run_root = _reject_symlink_components(run_root, label="run root")
    if run_root.parent.name != VERIFICATION_RUNS_DIR_NAME:
        raise SystemExit(
            f"run root must be under <main-root>/{VERIFICATION_RUNS_DIR_NAME}: {run_root}"
        )
    return _reject_symlink_components(run_root.parent.parent, label="main root")


def _owned_directory(parent: Path, name: str) -> Path:
    """Create one controller-owned directory without following a symlink."""

    owner = _reject_symlink_components(parent, label="controller-owned parent")
    path = owner / name
    if path.is_symlink():
        raise SystemExit(f"controller-owned directory cannot be a symlink: {path}")
    _reject_symlink_components(path, label="controller-owned directory")
    path.mkdir(parents=True, exist_ok=True)
    _reject_symlink_components(path, label="controller-owned directory")
    return path


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
            _owned_directory(existing, RUN_BUILDS_DIR_NAME)
            _owned_directory(existing, ANNOTATION_HISTORY_DIR_NAME)
            reports_root(existing)
            return existing
    stamp = timestamp or datetime.now().strftime("%Y%m%d%H%M%S")
    base_name = f"{slug(case_name)}-{stamp}"
    parent = _owned_directory(main_root, VERIFICATION_RUNS_DIR_NAME)
    report_parent = _owned_directory(main_root, REPORTS_DIR_NAME)
    suffix = 0
    while True:
        if suffix > 99:
            raise SystemExit(
                f"no free paired run/report suffix remains for {base_name}"
            )
        name = base_name if suffix == 0 else f"{base_name}-{suffix:02d}"
        run_root = parent / name
        report_root = report_parent / name
        # An orphan/stale report root is a collision, never reusable state for
        # a newly allocated run. The run directory itself is the first atomic
        # reservation; report creation then either completes the pair or the
        # still-empty reservation is removed and the next suffix is tried.
        if os.path.lexists(report_root):
            suffix += 1
            continue
        try:
            run_root.mkdir(exist_ok=False)
        except FileExistsError:
            suffix += 1
            continue
        try:
            report_root.mkdir(exist_ok=False)
            _reject_symlink_components(report_root, label="report root")
        except FileExistsError:
            try:
                run_root.rmdir()
            except OSError as exc:
                raise SystemExit(
                    "paired report allocation collided and the newly reserved "
                    f"empty run root could not be removed: {run_root}: {exc}"
                ) from exc
            suffix += 1
            continue
        except BaseException:
            with suppress(OSError):
                run_root.rmdir()
            raise
        break
    _owned_directory(run_root, RUN_BUILDS_DIR_NAME)
    _owned_directory(run_root, ANNOTATION_HISTORY_DIR_NAME)
    return run_root


def run_builds_root(run_root: Path) -> Path:
    return _owned_directory(run_root, RUN_BUILDS_DIR_NAME)


def annotation_history_root(run_root: Path) -> Path:
    return _owned_directory(run_root, ANNOTATION_HISTORY_DIR_NAME)


def reports_root(run_root: Path) -> Path:
    run_root = _reject_symlink_components(run_root, label="run root")
    parent = _owned_directory(main_root_from_run_root(run_root), REPORTS_DIR_NAME)
    return _owned_directory(parent, run_root.name)


def annotation_attempt_report_root(run_root: Path, attempt_number: int) -> Path:
    """Return the immutable report directory for one persistent-agent iteration."""

    attempts = _owned_directory(reports_root(run_root), ANNOTATION_ATTEMPTS_DIR_NAME)
    return _owned_directory(attempts, annotation_attempt_directory_name(attempt_number))


def annotation_attempt_directory_name(attempt_number: int) -> str:
    """Return the compact directory identity shared by report and history."""

    if attempt_number < 1:
        raise ValueError("annotation attempt number must be positive")
    return f"{ANNOTATION_ATTEMPT_DIR_PREFIX}{attempt_number}"


def controller_state_path(run_root: Path) -> Path:
    return reports_root(run_root) / CONTROLLER_STATE_FILE_NAME


def run_logs_path(run_root: Path) -> Path:
    return reports_root(run_root) / "run_logs.json"


def round_report_root(run_root: Path, round_id: str) -> Path:
    rounds = _owned_directory(reports_root(run_root), "rounds")
    return _owned_directory(rounds, slug(round_id))


def prepare_group_directory(
    *,
    groups_root: Path,
    group_id: str,
    index: int,
    files: dict[str, bytes],
    run_root: Path,
    force: bool = False,
) -> Path:
    """Write independent group files from one current preparation read."""

    if any(Path(name).name != name for name in files):
        raise ValueError("group file names must be direct children")

    groups_root = fixed_path_under(
        groups_root, run_root, label="vc-proving groups directory"
    )
    groups_root.mkdir(parents=True, exist_ok=True)
    directory = groups_root / f"group_{index:02d}__{slug(group_id)}"
    fixed_path_under(directory, run_root, label="fixed group directory")
    if directory.exists():
        if not force:
            raise SystemExit(
                f"group directory already exists: {directory}; pass --force-groups to replace it"
            )
        shutil.rmtree(directory)
    directory.mkdir(parents=True)
    for name, payload in files.items():
        atomic_write_bytes(directory / name, payload)
    return directory


def write_json(path: Path, payload: dict[str, Any]) -> None:
    write_bytes(
        path,
        (json.dumps(payload, indent=2, ensure_ascii=True) + "\n").encode("utf-8"),
        label="controller JSON output",
    )


def write_text(path: Path, text: str) -> None:
    write_bytes(
        path,
        (text.rstrip() + "\n").encode("utf-8"),
        label="controller text output",
    )


def write_bytes(
    path: Path, payload: bytes, *, label: str = "controller binary output"
) -> None:
    """Atomically replace one fixed leaf without trusting a predictable temp.

    A deterministic ``<name>.tmp`` can itself be pre-created as a symlink.
    ``mkstemp`` creates a new regular file in the already validated parent,
    after which ``os.replace`` swaps the fixed destination atomically.
    """

    path = _reject_symlink_components(path, label=label)
    path.parent.mkdir(parents=True, exist_ok=True)
    _reject_symlink_components(path.parent, label=f"{label} parent")
    atomic_write_bytes(path, payload)


def render_group_worker_input(
    group: dict[str, Any], *, formal_case_lib: str | None, report_dir: Path,
    commands: dict[str, Any], repair_index: int = 0, repair_feedback: str | None = None,
) -> str:
    """Render only the current assignment; the skill owns shared proof rules."""
    root = Path(commands["check"]["cwd"])
    skill = Path(__file__).resolve().parents[2] / "skills/group-worker-proving/SKILL.md"
    witnesses = []
    editable = []
    protected = []
    for witness in group["witnesses"]:
        name, mode = witness["name"], witness["proof_mode"]
        editable.append(name)
        lines = [f"### `{name}` — `{mode}`"]
        if mode == "aggressive_pre_process":
            editable.extend(item["name"] for item in witness["split_goals"])
            lines.extend(f"- Split `{item['name']}`: {item['strategy']}" for item in witness["split_goals"])
        else:
            lines.append(witness["strategy"])
            protected.extend(item["name"] for item in witness["split_goals"])
        witnesses.append("\n\n".join(lines))
    helper_lines = "\n".join(
        f"- `{helper['name']}` ({helper['visibility']}): {helper['strategy']}"
        for helper in group["helpers"]
    ) or "- None planned."
    if formal_case_lib is None:
        library = "No case library exists: do not create helpers, imports, or a library."
    else:
        library = (
            f"- Group library: `{group['group_worker_lib']}`\n"
            f"- Read-only canonical library: `{root / formal_case_lib}`\n"
            f"- Every new/adapted helper uses suffix `{group['helper_namespace']['suffix']}`. Preserve the seed."
        )
    repair = (
        f"\n## Current repair {repair_index}\n\n{repair_feedback}\n"
        if repair_feedback else ""
    )
    invocations = {name: commands[name] for name in ("debug", "development", "check")}
    return f"""# Group worker handoff

Read `{skill}` and its required workflow documents completely. Use this assignment without relying on a parent transcript or current sibling output.

- Group: `{group['id']}`; difficulty hint: {group['estimated_difficulty']}/5.
- Copied manual: `{group['proof_manual']}`.
- Editable proof spans: {', '.join(f'`{name}`' for name in editable)}.
- Protected LLM split blocks (keep generated Proof/Abort tokens): {', '.join(f'`{name}`' for name in protected) or 'none'}.
- Statements, declaration order, prelude and all unassigned proof tokens remain fixed. Formatting is ignored.
{library}

{chr(10).join(witnesses)}

## Helpers

{helper_lines}

## Historical references

- Previous proving round: `{group.get('previous_proving_round') or 'none'}`.
- Annotation history: `{group['annotation_history_directory']}`; earlier canonical proofs may be in an attempt's `before` directory.
- Optional human reuse note: `{group['proof_reuse']}`.

Search relevant historical blocks when useful. The controller does not search, copy, or rename historical proofs. Decide whether to adapt them and recheck against current inputs.
{repair}
## Commands

Use these exact argv/cwd objects. Shell-only tools may quote each argument for the actual shell; PowerShell uses `&` with single-quoted arguments and doubled embedded apostrophes. Follow the skill for proof modes, safety, and checks.

```json
{json.dumps(invocations, ensure_ascii=False, indent=2)}
```

Debug script: `{commands['debug_script']}`. Continue each live tool session until its actual exit. Successful checks require both exit zero and JSON status passed.

## Delivery

- Notes: `{report_dir / 'group_worker_output.md'}`; annotation-gap requires a nonempty explanation.
- Terminal report: `{report_dir / 'group_worker_report.json'}`.

Use the skill's exact completed/blocked report contract. Stop writing before main finalizes. The group directory contains only its copied manual and, when provided, group library. Finalization validates the current files.
"""


def build_group_worker_report_payload() -> dict[str, Any]:
    return {
        "status": "pending",
    }


def init_group_worker_files(
    *,
    report_dir: Path,
    group: dict[str, Any],
    formal_case_lib: str | None,
    commands: dict[str, Any],
) -> None:
    report_dir = _reject_symlink_components(report_dir, label="group report directory")
    write_text(
        report_dir / "group_worker_input.md",
        render_group_worker_input(
            group,
            formal_case_lib=formal_case_lib,
            report_dir=report_dir,
            commands=commands,
        ),
    )
    write_json(
        report_dir / "group_worker_report.json",
        build_group_worker_report_payload(),
    )
