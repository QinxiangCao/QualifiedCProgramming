#!/usr/bin/env python3
"""Internal canonical symbolic-execution implementation used by controller.py.

The controller supplies the repository root, target C file, and output root.
This module selects the platform driver and constructs the required include,
SLP, logic, generated-file, input-file, and cwd arguments.
"""

# ruff: noqa: E402 -- this internal module resolves vc-proving path helpers at runtime.

from __future__ import annotations

import math
import os
import platform
import re
import shutil
import stat
import sys
import time
from collections import deque
from collections.abc import Callable, Mapping
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parent / "vc-proving"
sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from file_integrity import (
    _fixed_artifact_leaf, _lexical_regular_file_snapshot,
    _metadata_is_link_like, _snapshot_text,
)
from path_utils import fixed_path_under, path_is_link_like, target_files_for_c, write_json
from process_adapter import run_bounded_process
from proof_manual_utils import (
    coq_token_text,
    generated_artifact_module_spellings,
    parse_manual,
    required_rocq_modules,
)
GENERATED_FILE_KEYS = (
    "goal_file",
    "proof_auto_file",
    "proof_manual_file",
    "goal_check_file",
)
MANDATORY_GENERATED_FILE_KEYS = (
    "goal_file",
    "proof_auto_file",
    "goal_check_file",
)
QUOTED_INCLUDE_RE = re.compile(
    r'^\s*#\s*include\s*"(?P<path>[^"\r\n]+)"', re.MULTILINE
)
ANNOTATION_BLOCK_RE = re.compile(r"/\*@(?P<body>.*?)\*/", re.DOTALL)
STRATEGY_INCLUDE_RE = re.compile(
    r'\binclude\s+strategies\s+"(?P<path>[^"\r\n]+)"'
)
ROCQ_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
# Planning and the single driver call share one bounded command budget.
SYMEXEC_TIMEOUT_SECONDS = 3600
DEFAULT_SYMEXEC_PROFILE = "standard"
SYMEXEC_PROFILES: dict[str, dict[str, int | str]] = {
    "standard": {
        "name": "standard",
        "timeout_seconds": SYMEXEC_TIMEOUT_SECONDS,
        "heartbeat_seconds": 30,
        "poll_interval_seconds": 5,
    },
    "recursive-large": {
        "name": "recursive-large",
        "timeout_seconds": 7200,
        "heartbeat_seconds": 30,
        "poll_interval_seconds": 5,
    },
}
STRATEGY_PROFILE_BY_COLLECTION = {
    "Applications_human": "QCP_demos_human",
    "LLM_bench": "QCP_demos_LLM",
    "QCP_demos_LLM": "QCP_demos_LLM",
    "QCP_demos_human": "QCP_demos_human",
    "QCP_demos_tutorial": "QCP_demos_tutorial",
}
STRATEGY_PROFILE_BY_TARGET_PREFIX: dict[tuple[str, ...], str | None] = {
    ("Applications_human", "convex_hull"): "QCP_demos_LLM",
    ("Applications_human", "fme_ge_gmp"): None,
}
SYMEXEC_FLAGS_BY_TARGET_PREFIX: dict[tuple[str, ...], tuple[str, ...]] = {
    ("LLM_bench", "Algorithms", "convex_hull_float"): ("--float-finite-vc",),
}


def symexec_profile_record(name: str | None = None) -> dict[str, int | str]:
    """Return one controller-owned, auditable performance profile."""

    selected = name or DEFAULT_SYMEXEC_PROFILE
    profile = SYMEXEC_PROFILES.get(selected)
    if profile is None:
        raise ValueError(
            "unknown symexec profile; expected one of: "
            + ", ".join(sorted(SYMEXEC_PROFILES))
        )
    return dict(profile)


def symexec_profile_for_state(state: Mapping[str, Any]) -> dict[str, int | str]:
    """Validate the controller-selected performance profile."""

    value = state.get("symexec_profile")
    if value is None:
        return symexec_profile_record()
    if not isinstance(value, Mapping):
        raise ValueError("controller symexec_profile must be an object")
    name = value.get("name")
    if not isinstance(name, str):
        raise ValueError("controller symexec_profile.name must be a string")
    expected = symexec_profile_record(name)
    if dict(value) != expected:
        raise ValueError(
            "controller symexec_profile differs from the named immutable profile"
        )
    return expected


def _tail(text: str, limit: int = 8000) -> str:
    return text if len(text) <= limit else text[-limit:]


def _utc() -> str:
    return (
        datetime.now(UTC)
        .isoformat(timespec="microseconds")
        .replace("+00:00", "Z")
    )


def _generated_progress_snapshot(output_root: Path, target_files: Mapping[str, str]) -> dict[str, Any]:
    """Report actual output sizes without parsing files that are still being written."""
    records = []
    for role in GENERATED_FILE_KEYS:
        record: dict[str, Any] = {"role": role, "state": "missing", "size": 0}
        try:
            path = _fixed_artifact_leaf(root=output_root, relative=target_files[role], label=f"symexec progress {role}")
            metadata = os.lstat(path)
            if _metadata_is_link_like(metadata) or not stat.S_ISREG(metadata.st_mode):
                raise ValueError("generated output is not a non-link regular file")
            record.update(state="present", size=metadata.st_size)
        except FileNotFoundError:
            pass
        except (OSError, ValueError) as exc:
            record.update(state="invalid", message=str(exc))
        records.append(record)
    return {"generated_files": records, "generated_bytes": sum(item["size"] for item in records)}


def _progress_reporter(
    *, main_root: Path, output_root: Path, target_files: Mapping[str, str],
    progress_path: Path | None, heartbeat_seconds: float, timeout_seconds: float, profile_name: str,
) -> tuple[Callable[[float, str, str], None], Callable[[str, float, str, str], None]]:
    path = (_input_path(progress_path, main_root, label="symexec progress report")
            if progress_path is not None else None)
    last_written = -math.inf

    def write(status: str, elapsed: float, stdout: str, stderr: str, *, force: bool = False) -> None:
        nonlocal last_written
        if path is None or (not force and elapsed - last_written < heartbeat_seconds):
            return
        last_written = elapsed
        lines = (stderr + "\n" + stdout).strip().splitlines()
        try:
            write_json(path, {
                "status": status, "updated_at": _utc(), "elapsed_seconds": round(elapsed, 3),
                "timeout_seconds": timeout_seconds, "profile": profile_name,
                "last_output_line": _tail(lines[-1].strip(), 500) if lines else "",
                **_generated_progress_snapshot(output_root, target_files),
            })
        except (OSError, SystemExit, ValueError):
            # Progress is diagnostic; an unavailable log cannot change proof acceptance.
            pass

    def progress(elapsed: float, stdout: str, stderr: str) -> None:
        write("running", elapsed, stdout, stderr)

    def finish(status: str, elapsed: float, stdout: str, stderr: str) -> None:
        write(status, elapsed, stdout, stderr, force=True)

    return progress, finish


def _normalize_generated_freshness_text(text: str, root: Path) -> str:
    """Ignore the selected output root and platform line endings, nothing else."""
    root_text = str(root.expanduser().resolve())
    for spelling in sorted({root_text, root_text.replace("\\", "/"), root_text.replace("/", "\\")},
                           key=len, reverse=True):
        text = text.replace(spelling, "$QCP_OUTPUT_ROOT")
    return text.replace("\r\n", "\n")


def _generated_artifact_snapshots(
    plan: Mapping[str, Any], output: Path,
) -> dict[str, dict[str, Any]]:
    return {role: _lexical_regular_file_snapshot(
        root=output, relative=str(plan["target_files"][role]), label=f"generated output {role}",
    ) for role in GENERATED_FILE_KEYS}


def _generated_snapshot_records(
    plan: Mapping[str, Any], snapshots: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    return [{"role": role, "relative_path": str(plan["target_files"][role]),
             "state": str(snapshots[role].get("state") or "invalid")}
            for role in GENERATED_FILE_KEYS]


def _output_problem(
    target_files: Mapping[str, str], role: str, kind: str, message: str,
) -> dict[str, str]:
    return {
        "category": "generated-output", "kind": kind, "role": role,
        "relative_path": target_files[role], "message": message,
        "repair": "Correct the source annotation or generator failure, then rerun the controller symexec command; do not edit generated files.",
    }


def _generated_preflight_failure(
    plan: Mapping[str, Any], snapshots: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any] | None:
    for role, snapshot in snapshots.items():
        if snapshot.get("state") not in {"present", "missing"}:
            return {
                **_output_problem(plan["target_files"], role, "generated-output-path-invalid",
                                  str(snapshot.get("message") or "generated path is not a non-link regular file")),
                "category": "structure",
                "repair": "Restore the exact generated path and its ancestors to ordinary non-link files/directories, then rerun symexec.",
            }
    return None


def _generated_output_failure(
    plan: dict[str, Any], output: Path, *,
    snapshots: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any] | None:
    """Validate one output bundle; a manual is optional unless goal-check imports it."""
    current = _generated_artifact_snapshots(plan, output) if snapshots is None else snapshots
    if set(current) != set(GENERATED_FILE_KEYS):
        raise ValueError("generated output snapshot set is incomplete")
    target = plan["target_files"]
    texts: dict[str, str] = {}
    for role in (*MANDATORY_GENERATED_FILE_KEYS, "proof_manual_file"):
        snapshot = current[role]
        state = snapshot.get("state")
        if state == "missing" and role == "proof_manual_file":
            continue
        if state != "present":
            kind = {"missing": "missing", "unreadable": "unreadable", "nonregular": "nonregular"}.get(state, "invalid")
            return _output_problem(target, role, f"generated-file-{kind}",
                                   str(snapshot.get("message") or "symexec did not create a required generated file"))
        if snapshot.get("size") == 0:
            return _output_problem(target, role, "generated-file-empty", "symexec returned a zero-byte generated file")
        try:
            texts[role] = _snapshot_text(snapshot, label=f"generated output {role}")
        except ValueError as exc:
            return _output_problem(target, role, "generated-file-invalid", str(exc))
    if "proof_manual_file" not in texts:
        try:
            imports = required_rocq_modules(texts["goal_check_file"], source_label="<generated-goal-check>")
        except ValueError as exc:
            return _output_problem(target, "goal_check_file", "goal-check-contract", str(exc))
        manual_modules = generated_artifact_module_spellings(target, roles=("proof_manual_file",))
        if not manual_modules.isdisjoint(imports):
            return _output_problem(target, "proof_manual_file", "generated-file-missing",
                                   "generated goal-check imports a proof manual that symexec did not create")
    else:
        try:
            parse_manual(texts["proof_manual_file"])
        except ValueError as exc:
            return _output_problem(target, "proof_manual_file", "proof-manual-contract", str(exc))
    return None


def clean_output_freshness(
    *, main_root: Path, target_c_file: Path, target_files: dict[str, str],
    reference_root: Path, refresh_root: Path, manual_mode: str,
    symexec_runner: Callable[..., dict[str, Any]] | None = None,
    timeout_seconds: int | float | None = None,
    profile_name: str = DEFAULT_SYMEXEC_PROFILE,
    heartbeat_seconds: int | float = 30,
    cancel_requested: Callable[[], bool] | None = None,
    progress_path: Path | None = None,
) -> dict[str, Any]:
    """Generate separately, then compare raw files or the proved manual's obligations."""
    if manual_mode not in {"raw", "proved"}:
        raise ValueError("manual_mode must be raw or proved")
    refresh = _validate_output_root(main_root, refresh_root)
    if refresh == main_root or refresh == reference_root:
        raise ValueError("freshness output must be separate from the main and reference roots")
    existed = os.path.lexists(refresh)
    if existed:
        if not refresh.is_dir():
            raise ValueError("freshness output is not an ordinary directory")
        shutil.rmtree(refresh)
    refresh.mkdir(parents=True)
    result = (symexec_runner or run_symexec)(
        main_root=main_root, target_c_file=target_c_file, target_files=target_files,
        output_root=refresh, timeout_seconds=timeout_seconds, profile_name=profile_name,
        heartbeat_seconds=heartbeat_seconds, cancel_requested=cancel_requested, progress_path=progress_path,
    )
    mismatches: list[dict[str, Any]] = []
    if result.get("status") == "passed":
        plan = {"target_files": target_files}
        previous = _generated_artifact_snapshots(plan, reference_root)
        fresh = _generated_artifact_snapshots(plan, refresh)
        for role in GENERATED_FILE_KEYS:
            before, after = previous[role], fresh[role]
            if role == "proof_manual_file" and before.get("state") == after.get("state") == "missing":
                continue
            kind = "manual-witness-statements" if role == "proof_manual_file" and manual_mode == "proved" else role
            try:
                before_text = _snapshot_text(before, label=f"current {role}")
                after_text = _snapshot_text(after, label=f"fresh {role}")
                if kind == "manual-witness-statements":
                    declarations = []
                    for text in (before_text, after_text):
                        declarations.append([(name, coq_token_text(vc["statement"]))
                                             for name, vc in parse_manual(text).vc_index["by_name"].items()])
                    equal = declarations[0] == declarations[1]
                else:
                    equal = (_normalize_generated_freshness_text(before_text, reference_root)
                             == _normalize_generated_freshness_text(after_text, refresh))
                if not equal:
                    mismatches.append({"kind": kind, "relative_path": target_files[role]})
            except ValueError as exc:
                mismatches.append({"kind": kind, "relative_path": target_files[role], "message": str(exc)})
    return {
        "status": "passed" if result.get("status") == "passed" and not mismatches else "failed",
        "symexec": {key: result[key] for key in (
            "status", "returncode", "timeout_seconds", "performance_profile", "progress_path", "first_failure", "elapsed_seconds",
        ) if result.get(key) is not None},
        "mismatches": mismatches, "refresh_root": str(refresh),
        "interrupted_output_recovery": {"status": "cleaned" if existed else "not-needed"},
    }


def _input_path(path: Path, root: Path, *, label: str) -> Path:
    """Keep lexical paths until their link/reparse and owner checks finish."""

    try:
        return fixed_path_under(path, root, label=label)
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc


def _relative_target(main_root: Path, target_c_file: Path) -> Path:
    target = target_c_file.expanduser()
    if not target.is_absolute():
        target = main_root / target
    target = _input_path(target, main_root, label="target C file")
    try:
        relative = target.relative_to(main_root)
    except ValueError as exc:
        raise ValueError(f"target C file must be under main root: {target}") from exc
    if not target.is_file():
        raise ValueError(f"target C file does not exist: {target}")
    return relative


def _validate_output_root(main_root: Path, output_root: Path) -> Path:
    output = _input_path(output_root, main_root, label="symexec output root")
    if output == main_root:
        return output
    allowed = (main_root / "verification_runs", main_root / "reports")
    if any(output.is_relative_to(root) for root in allowed):
        return output
    raise ValueError(
        f"output root must be the main root or be under main-root/verification_runs or main-root/reports: {output}"
    )


def _runtime_platform() -> tuple[str, str, str]:
    return os.name, sys.platform, platform.machine()


def _driver_for_platform(main_root: Path) -> Path:
    os_name, platform_name, machine = _runtime_platform()
    normalized_machine = machine.strip().lower()

    if os_name == "nt":
        return main_root / "win-binary" / "symexec.exe"
    if platform_name.startswith("linux"):
        if normalized_machine not in {"x86_64", "amd64"}:
            raise ValueError(
                f"unsupported Linux architecture for bundled symexec: {machine or '<unknown>'}"
            )
        return main_root / "linux-binary" / "symexec"
    if platform_name == "darwin":
        if normalized_machine in {"arm64", "aarch64"}:
            return main_root / "mac-arm64-binary" / "symexec"
        if normalized_machine in {"x86_64", "amd64"}:
            return main_root / "mac-x86-64-binary" / "symexec"
        raise ValueError(
            f"unsupported macOS architecture for symexec: {machine or '<unknown>'}"
        )
    raise ValueError(
        "unsupported platform for symexec: "
        f"os.name={os_name!r}, sys.platform={platform_name!r}, machine={machine!r}"
    )


def _c_without_comments(text: str) -> str:
    """Mask C comments so commented-out include directives are never followed."""

    output: list[str] = []
    index = 0
    in_block = False
    in_line = False
    quote: str | None = None
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if in_block:
            if pair == "*/":
                output.extend("  ")
                in_block = False
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_line:
            if char == "\n":
                in_line = False
                output.append(char)
            else:
                output.append(" ")
            index += 1
            continue
        if quote is None and pair == "/*":
            in_block = True
            output.extend("  ")
            index += 2
            continue
        if quote is None and pair == "//":
            in_line = True
            output.extend("  ")
            index += 2
            continue
        output.append(char)
        if quote is not None:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
        elif char in {'"', "'"}:
            quote = char
        index += 1
    if in_block:
        raise ValueError("unterminated C block comment while resolving quoted includes")
    return "".join(output)


def _source_includes(source: Path) -> tuple[list[str], list[str]]:
    """Read a C/header/strategy source once for its two include forms."""
    try:
        text = source.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise ValueError(f"cannot read include source {source}: {exc}") from exc
    headers = [match.group("path").strip() for match in QUOTED_INCLUDE_RE.finditer(_c_without_comments(text))]
    strategies = [match.group("path").strip() for annotation in ANNOTATION_BLOCK_RE.finditer(text)
                  for match in STRATEGY_INCLUDE_RE.finditer(annotation.group("body"))]
    if any(not path or "\0" in path for path in [*headers, *strategies]):
        raise ValueError(f"empty or invalid include path in {source}")
    return list(dict.fromkeys(headers)), list(dict.fromkeys(strategies))


def _resolve_include(
    *, qcp_root: Path, source: Path, name: str, include_dirs: list[Path],
    profile_dirs: tuple[Path, ...], repository_index: dict[str, list[Path]],
) -> tuple[Path, Path]:
    """Use local/collection/profile precedence, then require an unambiguous fallback."""
    relative = Path(name.replace("\\", "/"))
    if not relative.parts or relative.is_absolute() or relative.drive:
        raise ValueError(f"include must be relative to QCP_examples: {name!r} from {source}")
    local = _input_path(source.parent / relative, qcp_root, label="local include")
    if local.is_file():
        return local, source.parent
    if ".." in relative.parts:
        raise ValueError(f"cannot resolve confined include {name!r} from {source}")
    collection = qcp_root / source.relative_to(qcp_root).parts[0]
    for directory in (collection, *profile_dirs):
        candidate = _input_path(directory / relative, qcp_root, label="collection/profile include")
        if candidate.is_file():
            return candidate, directory
    matches: dict[Path, Path] = {}
    for directory in include_dirs:
        candidate = _input_path(directory / relative, qcp_root, label="known include")
        if candidate.is_file():
            matches[candidate] = directory
    if not matches:
        if not repository_index:
            def scan_error(error: OSError) -> None:
                raise error
            for directory, directories, files in os.walk(qcp_root, onerror=scan_error):
                parent = Path(directory)
                directories[:] = [name for name in directories if not path_is_link_like(parent / name)]
                for leaf in files:
                    repository_index.setdefault(os.path.normcase(leaf), []).append(parent / leaf)
        parts = tuple(os.path.normcase(part) for part in relative.parts)
        for candidate in repository_index.get(os.path.normcase(relative.name), []):
            tail = candidate.relative_to(qcp_root).parts[-len(parts):]
            if tuple(os.path.normcase(part) for part in tail) != parts:
                continue
            candidate = _input_path(candidate, qcp_root, label="repository include")
            if candidate.is_file():
                matches[candidate] = candidate.parents[len(parts) - 1]
    if len(matches) == 1:
        return next(iter(matches.items()))
    if matches:
        raise ValueError(f"ambiguous include {name!r} from {source}: " + ", ".join(str(path) for path in sorted(matches)))
    raise ValueError(f"cannot resolve include {name!r} from {source} under QCP_examples")


def _strategy_profile_directories(
    qcp_root: Path,
    target_relative: Path,
) -> tuple[Path, ...]:
    """Return the repository-defined strategy profile for one target path."""

    target_parts = target_relative.parts
    target_collection = target_parts[0]
    profile_collection = STRATEGY_PROFILE_BY_COLLECTION.get(target_collection)
    for prefix, override in sorted(
        STRATEGY_PROFILE_BY_TARGET_PREFIX.items(),
        key=lambda item: len(item[0]),
        reverse=True,
    ):
        if target_parts[: len(prefix)] == prefix:
            profile_collection = override
            break
    if profile_collection is None:
        return ()
    profile_root = _input_path(qcp_root / profile_collection, qcp_root, label="strategy profile")
    if not profile_root.is_dir():
        raise ValueError(
            "strategy profile directory is missing for "
            f"QCP_examples/{target_collection}: {profile_root}"
        )
    return (profile_root,)


def _relative_directory_argument(path: Path, main_root: Path) -> str:
    relative = path.resolve().relative_to(main_root).as_posix()
    return relative.rstrip("/") + "/"


def _strategy_directory_pair(
    directory: Path,
    *,
    main_root: Path,
    qcp_root: Path,
) -> tuple[str, str]:
    relative = directory.resolve().relative_to(qcp_root)
    if not relative.parts or any(
        ROCQ_IDENTIFIER_RE.fullmatch(part) is None for part in relative.parts
    ):
        raise ValueError(
            "strategy directory cannot form an SLP logical path: "
            + relative.as_posix()
        )
    if relative.parts[0] == "stdlib":
        logical = "SimpleC.StdLib" + (
            "." + ".".join(relative.parts[1:])
            if len(relative.parts) > 1
            else ""
        )
    else:
        logical = "SimpleC.EE." + ".".join(relative.parts)
    return _relative_directory_argument(directory, main_root), logical


def _extra_symexec_flags(target_relative: Path) -> tuple[str, ...]:
    try:
        qcp_relative = target_relative.relative_to("QCP_examples")
    except ValueError:
        return ()
    for prefix, flags in sorted(
        SYMEXEC_FLAGS_BY_TARGET_PREFIX.items(),
        key=lambda item: len(item[0]),
        reverse=True,
    ):
        if qcp_relative.parts[: len(prefix)] == prefix:
            return flags
    return ()


def _symexec_search_paths(
    main_root: Path, target_rel: Path
) -> tuple[list[str], list[tuple[str, str]]]:
    """Discover include roots plus exact-strategy and collection SLP pairs."""

    qcp_root = _input_path(main_root / "QCP_examples", main_root, label="QCP input root")
    target = _input_path(main_root / target_rel, qcp_root, label="target C file")
    try:
        target_relative = target.relative_to(qcp_root)
    except ValueError as exc:
        raise ValueError(f"target C escaped QCP_examples: {target}") from exc
    if len(target_relative.parts) < 2:
        raise ValueError(f"target C lacks a QCP_examples collection: {target}")
    strategy_profile_dirs = _strategy_profile_directories(
        qcp_root,
        target_relative,
    )
    include_dirs: list[Path] = [target.parent]
    source_queue = deque([target])
    repository_index: dict[str, list[Path]] = {}
    visited: set[Path] = set()
    collections: list[str] = []
    strategy_directories: list[Path] = []

    while source_queue:
        source = source_queue.popleft().resolve()
        if source in visited:
            continue
        visited.add(source)
        try:
            source_relative = source.relative_to(qcp_root)
        except ValueError as exc:
            raise ValueError(
                f"quoted include escaped QCP_examples: {source}"
            ) from exc
        if len(source_relative.parts) < 2:
            raise ValueError(f"include source lacks a QCP_examples collection: {source}")
        collection = source_relative.parts[0]
        if ROCQ_IDENTIFIER_RE.fullmatch(collection) is None:
            raise ValueError(
                f"QCP_examples collection cannot form an SLP module: {collection!r}"
            )
        if collection not in collections:
            collections.append(collection)
        headers, strategies = _source_includes(source)
        for names, strategy in ((headers, False), (strategies, True)):
            for name in names:
                included, search_root = _resolve_include(
                    qcp_root=qcp_root, source=source, name=name, include_dirs=include_dirs,
                    profile_dirs=strategy_profile_dirs, repository_index=repository_index,
                )
                if strategy:
                    if included.parent not in strategy_directories:
                        strategy_directories.append(included.parent)
                elif search_root not in include_dirs:
                    include_dirs.append(search_root)
                if included not in visited:
                    source_queue.append(included)

    # A collection's default strategy profile participates even when the C
    # include graph does not name one of its headers directly.  This preserves
    # the existing Applications_human/LLM_bench symexec environment while the
    # include traversal remains otherwise data-driven.
    for profile_dir in strategy_profile_dirs:
        if profile_dir not in include_dirs:
            include_dirs.append(profile_dir)
        profile_collection = profile_dir.relative_to(qcp_root).parts[0]
        if profile_collection not in collections:
            collections.append(profile_collection)

    include_args = [
        _relative_directory_argument(directory, main_root) for directory in include_dirs
    ]
    collection_pairs = [
        (
            f"QCP_examples/{collection}/",
            (
                "SimpleC.StdLib"
                if collection == "stdlib"
                else f"SimpleC.EE.{collection}"
            ),
        )
        for collection in collections
    ]
    slp_pairs: list[tuple[str, str]] = []
    for pair in (
        *(
            _strategy_directory_pair(
                directory,
                main_root=main_root,
                qcp_root=qcp_root,
            )
            for directory in strategy_directories
            if len(directory.resolve().relative_to(qcp_root).parts) > 1
        ),
        *collection_pairs,
    ):
        if pair not in slp_pairs:
            slp_pairs.append(pair)
    return include_args, slp_pairs


def _validated_target_files(
    *,
    target_rel: Path,
    target_files: Mapping[str, str],
) -> dict[str, str]:
    expected = target_files_for_c(target_rel, target_files.get("case_name"))
    if dict(target_files) != expected:
        raise ValueError("target_files does not match the canonical C/case topology")
    return expected


def build_symexec_plan(
    *,
    main_root: Path,
    target_c_file: Path,
    output_root: Path,
    target_files: Mapping[str, str],
) -> dict[str, Any]:
    main_root = main_root.expanduser().absolute()
    main_root = _input_path(main_root, main_root, label="main root")
    if (
        not (main_root / "QCP_examples").is_dir()
        or not (main_root / "Rocq").is_dir()
    ):
        raise ValueError(
            f"main root does not look like the QCP repository: {main_root}"
        )
    target_rel = _relative_target(main_root, target_c_file)
    output_root = _validate_output_root(main_root, output_root)
    planned_target_files = _validated_target_files(
        target_rel=target_rel,
        target_files=target_files,
    )
    driver = _driver_for_platform(main_root)
    include_args, slp_pairs = _symexec_search_paths(main_root, target_rel)
    argv = [
        str(driver),
        f"--goal-file={output_root / planned_target_files['goal_file']}",
        f"--proof-auto-file={output_root / planned_target_files['proof_auto_file']}",
        f"--proof-manual-file={output_root / planned_target_files['proof_manual_file']}",
    ]
    argv.extend(f"-I{directory}" for directory in include_args)
    for physical, logical in slp_pairs:
        argv.extend(("-slp", physical, logical))
    argv.extend(
        (
            f"--coq-logic-path={planned_target_files['active_case_theory']}",
            f"--input-file={planned_target_files['c_file']}",
        )
    )
    extra_flags = _extra_symexec_flags(target_rel)
    argv.extend(extra_flags)
    argv.append("--no-exec-info")
    return {
        "helper": str(Path(__file__).resolve()),
        "driver": str(driver),
        "cwd": str(main_root),
        "main_root": str(main_root),
        "output_root": str(output_root),
        "target_c_file": planned_target_files["c_file"],
        "target_files": planned_target_files,
        "include_args": include_args,
        "slp_args": [item for pair in slp_pairs for item in pair],
        "extra_flags": list(extra_flags),
        "argv": argv,
    }


def run_symexec(
    *, main_root: Path, target_c_file: Path, output_root: Path,
    target_files: Mapping[str, str], timeout_seconds: int | float | None = None,
    profile_name: str = DEFAULT_SYMEXEC_PROFILE,
    heartbeat_seconds: int | float | None = None,
    poll_interval_seconds: int | float | None = None,
    cancel_requested: Callable[[], bool] | None = None,
    progress_path: Path | None = None,
) -> dict[str, Any]:
    """Plan, launch the driver once, and validate the resulting output bundle."""
    started = time.monotonic()
    profile = symexec_profile_record(profile_name)
    budget = float(profile["timeout_seconds"] if timeout_seconds is None else timeout_seconds)
    heartbeat = float(profile["heartbeat_seconds"] if heartbeat_seconds is None else heartbeat_seconds)
    poll_interval = float(profile["poll_interval_seconds"] if poll_interval_seconds is None else poll_interval_seconds)
    for label, value, allow_zero in (("timeout", budget, True), ("heartbeat", heartbeat, False), ("poll interval", poll_interval, False)):
        if not math.isfinite(value) or value < 0 or (value == 0 and not allow_zero):
            raise ValueError(f"symexec {label} must be finite and {'non-negative' if allow_zero else 'positive'}")
    plan = build_symexec_plan(main_root=main_root, target_c_file=target_c_file,
                              output_root=output_root, target_files=target_files)
    root, output, driver = Path(plan["cwd"]), Path(plan["output_root"]), Path(plan["driver"])
    progress, finish_progress = _progress_reporter(
        main_root=root, output_root=output, target_files=plan["target_files"], progress_path=progress_path,
        heartbeat_seconds=heartbeat, timeout_seconds=budget, profile_name=profile_name,
    )
    snapshots: dict[str, dict[str, Any]] = {}
    returncode: int | None = None
    stdout = stderr = ""

    def finish(failure: dict[str, Any] | None, *, status: str | None = None) -> dict[str, Any]:
        outcome = status or ("passed" if failure is None else "failed")
        elapsed = time.monotonic() - started
        finish_progress("cancelled" if returncode == 130 else outcome, elapsed, stdout, stderr or str((failure or {}).get("message") or ""))
        result: dict[str, Any] = {
            "target_c_file": plan["target_c_file"], "timeout_seconds": budget,
            "performance_profile": profile_name, "heartbeat_seconds": heartbeat,
            "status": outcome, "returncode": returncode, "elapsed_seconds": round(elapsed, 3),
            "generated_files": _generated_snapshot_records(plan, snapshots) if snapshots else [],
        }
        if progress_path is not None:
            result["progress_path"] = str(progress_path)
        if failure is not None:
            result.update(first_failure=failure, stdout_tail=_tail(stdout), stderr_tail=_tail(stderr))
        return result

    progress(time.monotonic() - started, "", "")
    if not driver.is_file() or (os.name != "nt" and not os.access(driver, os.X_OK)):
        kind = "driver-not-executable" if driver.is_file() else "driver-missing"
        return finish({"category": "tool", "kind": kind, "message": f"symexec driver is unavailable: {driver}",
                       "repair": "Restore the selected platform driver and its executable permission, then rerun the controller command."}, status="skipped")
    snapshots = _generated_artifact_snapshots(plan, output)
    failure = _generated_preflight_failure(plan, snapshots)
    if failure is not None:
        return finish(failure)
    try:
        formal = _input_path(output / plan["target_files"]["formal_directory"], output, label="generated formal directory")
        formal.mkdir(parents=True, exist_ok=True)
    except (OSError, ValueError) as exc:
        return finish({"category": "structure", "kind": "generated-output-directory-invalid", "message": str(exc),
                       "repair": "Restore the generated formal directory as an ordinary writable directory, then rerun symexec."})
    remaining = budget - (time.monotonic() - started)
    if remaining <= 0:
        returncode, stderr = 124, "Symbolic execution's shared deadline expired before launch."
    else:
        try:
            process = run_bounded_process(
                plan["argv"], cwd=plan["cwd"], timeout_seconds=remaining,
                timeout_message=f"\nsymexec timed out after {budget} seconds",
                detached_pipe_message="; output pipes remained open after process exit",
                launch_error_prefix="symexec could not be launched: ",
                cancel_requested=cancel_requested, cancel_message="\nsymexec cancelled by controller pause/cancel request",
                progress_callback=lambda _elapsed, out, err: progress(time.monotonic() - started, out, err),
                poll_interval_seconds=poll_interval, return_cancelled_result=True,
            )
            returncode, stdout, stderr = process.returncode, process.stdout, process.stderr
        except BaseException:
            finish_progress("interrupted", time.monotonic() - started, stdout, stderr)
            raise
    snapshots = _generated_artifact_snapshots(plan, output)
    if returncode == 0:
        return finish(_generated_output_failure(plan, output, snapshots=snapshots))
    category, kind = {130: ("control", "cancelled"), 124: ("tool", "timeout")}.get(returncode, ("symbolic-execution", "symexec-error"))
    return finish({
        "category": category, "kind": kind,
        "message": _tail(stderr or stdout, 1600).strip() or f"symexec exited with return code {returncode}",
        "repair": ("Resume the paused run explicitly, then rerun the same action." if returncode == 130
                   else "Inspect the tool output and repair the reported source or environment issue before rerunning the controller command."),
    })
