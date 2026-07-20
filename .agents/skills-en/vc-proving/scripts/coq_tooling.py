#!/usr/bin/env python3
"""Internal Coq implementation used by the controller workflow.

This module is the only active place that constructs Coq command arguments.
It obtains the executable path from ``SeparationLogic/CONFIGURE`` and the
Makefile's ``COQC`` convention, while keeping the repository's fixed ``-R``
and ``-Q`` mappings.  Every check in every run reuses the base-library ``.vo``
files produced by a prior full make in the main root, staging them into that
check's build workspace without recompiling their sources.  The current target
case is never trusted through old ``.vo`` files: its five formal modules are
removed from the build output and recompiled from the current sources and
overlays on every applicable check.
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any, Iterable


FIXED_LOAD_PATH_MAPPINGS: tuple[tuple[str, str, str], ...] = (
    ("-R", "SeparationLogic/SeparationLogic", "SimpleC.SL"),
    ("-R", "SeparationLogic/unifysl", "Logic"),
    ("-R", "SeparationLogic/sets", "SetsClass"),
    ("-R", "SeparationLogic/compcert_lib", "compcert.lib"),
    ("-R", "SeparationLogic/auxlibs", "AUXLib"),
    ("-R", "SeparationLogic/examples", "SimpleC.EE"),
    ("-R", "SeparationLogic/stdlib", "SimpleC.StdLib"),
    ("-R", "SeparationLogic/StrategyLib", "SimpleC.StrategyLib"),
    ("-R", "SeparationLogic/Common", "SimpleC.Common"),
    ("-R", "SeparationLogic/fixedpoints", "FP"),
    ("-R", "SeparationLogic/MonadLib", "MonadLib"),
    ("-R", "SeparationLogic/listlib", "ListLib"),
    ("-R", "SeparationLogic/MaxMinLib", "MaxMinLib"),
    ("-R", "SeparationLogic/GraphLib", "GraphLib"),
    ("-R", "SeparationLogic/SumLib", "SumLib"),
    ("-R", "SeparationLogic/tracelib", "TraceLib"),
    ("-R", "SeparationLogic/coq-record-update/src", "RecordUpdate"),
    ("-Q", "SeparationLogic/algorithms", "Algorithms"),
)
DEFAULT_COQC = "coqc"
DEFAULT_COQTOP = "coqtop"
MAKE_ASSIGNMENT_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*(\?=|:=|=)\s*(.*?)\s*$")
MAKE_VARIABLE_RE = re.compile(r"\$\(([^()]+)\)|\$\{([^{}]+)\}")
DIAGNOSTIC_RE = re.compile(
    r'File "(?P<file>[^"]+)", line (?P<line>\d+), characters (?P<characters>[0-9-]+):\s*\n(?P<message>.*?)(?=\nFile "|\Z)',
    re.DOTALL,
)
COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.DOTALL)
STANDARD_PREFIXES = (
    "Coq",
    "Ltac2",
)
VERIFICATION_RUNS_DIR_NAME = "verification_runs"
RUN_BUILDS_DIR_NAME = "_coq_builds"
RUN_ROOT_RE = re.compile(r"^.+-\d{14}(?:-\d{2})?$")
TARGET_CASE_SUFFIXES = (
    "_proof_manual",
    "_proof_auto",
    "_goal_check",
    "_goal",
    "_lib",
)
TARGET_CASE_MODULE_SUFFIXES = (
    "_lib.v",
    "_goal.v",
    "_proof_auto.v",
    "_proof_manual.v",
    "_goal_check.v",
)
COQ_SIDE_PRODUCT_SUFFIXES = (".vo", ".vos", ".vok", ".glob")


def fixed_flags() -> list[str]:
    flags: list[str] = []
    for flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS:
        flags.extend([flag, physical, logical])
    return flags


def _make_values(workspace_root: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    separation_logic = workspace_root.expanduser().resolve() / "SeparationLogic"
    for path in (separation_logic / "Makefile", separation_logic / "CONFIGURE"):
        if not path.is_file():
            continue
        for raw_line in path.read_text(encoding="utf-8").splitlines():
            line = raw_line.split("#", 1)[0]
            match = MAKE_ASSIGNMENT_RE.match(line)
            if match is None:
                continue
            name, operator, value = match.groups()
            if operator == "?=" and name in values:
                continue
            values[name] = value.strip()
    return values


def _expand_make_value(value: str, values: dict[str, str]) -> str:
    expanded = value
    for _ in range(20):
        replaced = MAKE_VARIABLE_RE.sub(lambda match: values.get(match.group(1) or match.group(2), ""), expanded)
        if replaced == expanded:
            return replaced.strip()
        expanded = replaced
    raise ValueError(f"recursive Makefile variable while resolving Coq executable: {value}")


def configured_coq_executable(workspace_root: Path, tool: str) -> str:
    """Resolve coqc/coqtop through the repository's Makefile configuration."""

    values = _make_values(workspace_root)
    if tool == "coqc":
        expression = values.get("COQC", "$(COQBIN)coqc$(SUF)")
        fallback = DEFAULT_COQC
    elif tool == "coqtop":
        expression = values.get("COQTOP", "$(COQBIN)coqtop$(SUF)")
        fallback = DEFAULT_COQTOP
    else:
        raise ValueError(f"unsupported Coq tool: {tool}")
    executable = _expand_make_value(expression, values)
    return executable or fallback


def make_coqc_argv(target_file: str | Path, *, workspace_root: Path | None = None) -> list[str]:
    target = Path(str(target_file)).as_posix()
    if " -o " in target or target == "-o":
        raise ValueError("coqc -o is forbidden")
    executable = configured_coq_executable(workspace_root, "coqc") if workspace_root is not None else DEFAULT_COQC
    return [executable, "-q", *fixed_flags(), target]


def make_coqtop_argv(debug_script: str | Path, *, workspace_root: Path | None = None) -> list[str]:
    script = Path(str(debug_script)).as_posix()
    executable = configured_coq_executable(workspace_root, "coqtop") if workspace_root is not None else DEFAULT_COQTOP
    return [executable, "-q", "-batch", *fixed_flags(), "-l", script]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tail(text: str, limit: int = 8000) -> str:
    if len(text) <= limit:
        return text
    return text[-limit:]


def extract_first_coq_diagnostic(output: str) -> dict[str, Any] | None:
    match = DIAGNOSTIC_RE.search(output)
    if not match:
        return None
    return {
        "file": match.group("file"),
        "line": int(match.group("line")),
        "characters": match.group("characters"),
        "message": match.group("message").strip(),
    }


def coqc_transient_retries() -> int:
    raw = os.environ.get("COQC_TRANSIENT_RETRIES", "2").strip()
    try:
        value = int(raw)
    except ValueError:
        return 2
    return max(0, value)


def infer_main_workspace_root(formal_or_run_path: Path) -> Path:
    resolved = formal_or_run_path.expanduser().resolve()
    candidate_self = resolved if resolved.is_dir() else resolved.parent
    if (candidate_self / "dune-project").is_file() or (candidate_self / "SeparationLogic").is_dir():
        return candidate_self.resolve()
    parts = resolved.parts
    if VERIFICATION_RUNS_DIR_NAME in parts:
        index = parts.index(VERIFICATION_RUNS_DIR_NAME)
        candidate = Path(*parts[:index])
        if (candidate / "dune-project").is_file() or (candidate / "SeparationLogic").is_dir():
            return candidate.resolve()
    for parent in (resolved if resolved.is_dir() else resolved.parent).parents:
        if (parent / "dune-project").is_file() or (parent / "SeparationLogic").is_dir():
            return parent.resolve()
    raise ValueError(f"cannot infer main root from {formal_or_run_path}")


def infer_controller_main_workspace_root(path: Path) -> Path:
    resolved = path.expanduser().resolve()
    if VERIFICATION_RUNS_DIR_NAME in resolved.parts:
        index = resolved.parts.index(VERIFICATION_RUNS_DIR_NAME)
        candidate = Path(*resolved.parts[:index])
        if (candidate / "dune-project").is_file() or (candidate / "SeparationLogic").is_dir():
            return candidate.resolve()
    return infer_main_workspace_root(path)


def build_workspace_layout_error(workspace_root: Path, build_workspace: Path) -> str | None:
    """Return a protocol error unless build output is in a run `_coq_builds`."""
    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    try:
        main_root = infer_controller_main_workspace_root(workspace_root)
    except ValueError:
        return None
    try:
        rel = build_workspace.relative_to(main_root / VERIFICATION_RUNS_DIR_NAME)
    except ValueError:
        return f"build workspace must be under <main-root>/verification_runs/<case>-YYYYMMDDHHMMSS/{RUN_BUILDS_DIR_NAME}/...; got {build_workspace}"
    if len(rel.parts) >= 3 and RUN_ROOT_RE.fullmatch(rel.parts[0]) and rel.parts[1] == RUN_BUILDS_DIR_NAME:
        return None
    return f"build workspace must be under <main-root>/verification_runs/<case>-YYYYMMDDHHMMSS/{RUN_BUILDS_DIR_NAME}/...; got {build_workspace}"


def relative_to_workspace(path: Path, workspace_root: Path) -> Path:
    return path.expanduser().resolve().relative_to(workspace_root.expanduser().resolve())


def infer_case_config(workspace_root: Path, case_dir: Path) -> dict[str, str]:
    workspace_root = workspace_root.expanduser().resolve()
    case_dir = case_dir.expanduser().resolve()
    rel = relative_to_workspace(case_dir, workspace_root)
    parts = rel.parts
    if "SeparationLogic" in parts and "examples" in parts:
        sep_index = parts.index("SeparationLogic")
        theory_parts = parts[sep_index + 2 :] if sep_index + 1 < len(parts) and parts[sep_index + 1] == "examples" else (case_dir.name,)
    else:
        theory_parts = (case_dir.name,)
    case_name = theory_parts[-1]
    rel_posix = rel.as_posix()
    return {
        "case_name": case_name,
        "active_theory": "SimpleC.EE." + ".".join(theory_parts),
        "physical_path": rel_posix,
        "check_file": f"{rel_posix}/{case_name}_goal_check.v",
        "proof_manual_file": f"{rel_posix}/{case_name}_proof_manual.v",
    }


def _copy_if_changed(src: Path, dest: Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists() and dest.stat().st_size == src.stat().st_size:
        try:
            if file_sha256(dest) == file_sha256(src):
                return
        except OSError:
            pass
    shutil.copy2(src, dest)


def mirror_sources(
    workspace_root: Path,
    build_workspace: Path,
    extra_relatives: Iterable[Path] = (),
    overlays: dict[Path, Path] | None = None,
) -> tuple[list[str], list[str]]:
    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    copied: list[str] = []
    roots = [Path(physical) for _flag, physical, _logical in FIXED_LOAD_PATH_MAPPINGS]
    for root in roots:
        (build_workspace / root).mkdir(parents=True, exist_ok=True)
        src_root = workspace_root / root
        if not src_root.is_dir():
            continue
        for src in src_root.rglob("*.v"):
            rel = src.relative_to(workspace_root)
            _copy_if_changed(src, build_workspace / rel)
            copied.append(rel.as_posix())
    for rel in extra_relatives:
        src = workspace_root / rel
        if src.is_file():
            _copy_if_changed(src, build_workspace / rel)
            copied.append(rel.as_posix())
    overlaid: list[str] = []
    for destination, source in (overlays or {}).items():
        destination = Path(destination.as_posix())
        if destination.is_absolute() or ".." in destination.parts:
            raise ValueError(f"overlay destination must be repository-relative: {destination}")
        source = source.expanduser().resolve()
        if not source.is_file():
            raise ValueError(f"overlay source is missing: {source}")
        if destination.suffix != ".v" or source.suffix != ".v":
            raise ValueError("Coq overlays must map .v source files to .v destinations")
        _copy_if_changed(source, build_workspace / destination)
        copied.append(destination.as_posix())
        overlaid.append(destination.as_posix())
    return sorted(set(copied)), sorted(set(overlaid))


def _target_case_identity(rel: Path) -> tuple[Path, str] | None:
    if rel.suffix != ".v":
        return None
    stem = rel.stem
    for suffix in TARGET_CASE_SUFFIXES:
        if stem.endswith(suffix) and len(stem) > len(suffix):
            return rel.parent, stem[: -len(suffix)]
    return None


def target_case_sources(
    target_rel: Path,
    *,
    group_check: dict[str, Any] | None = None,
    overlays: dict[Path, Path] | None = None,
) -> list[Path]:
    """Derive the five current-case modules whose old .vo files are untrusted."""

    candidates = [Path(target_rel.as_posix())]
    candidates.extend(Path(path.as_posix()) for path in (overlays or {}))
    config = group_check or {}
    case_theory = str(config.get("case_theory") or "").strip()
    for module in config.get("require_modules", []):
        logical = f"{case_theory}.{module}" if case_theory else str(module)
        relative = logical_module_to_relative(logical)
        if relative is not None:
            candidates.append(relative)
    identity = None
    for candidate in candidates:
        identity = _target_case_identity(candidate)
        if identity is not None:
            break
    if identity is None:
        return []
    directory, case_name = identity
    return [directory / f"{case_name}{suffix}" for suffix in TARGET_CASE_MODULE_SUFFIXES]


def _reuse_one_base_vo(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists() or destination.is_symlink():
        try:
            if os.path.samefile(source, destination):
                return
        except OSError:
            pass
        destination.unlink()
    try:
        os.link(source, destination)
    except OSError:
        try:
            destination.symlink_to(source)
        except OSError:
            # Windows or a cross-device build may reject both link forms.
            # Copying still reuses the built artifact without compiling source.
            shutil.copy2(source, destination)


def reuse_base_vo_files(
    workspace_root: Path,
    build_workspace: Path,
    *,
    excluded_sources: Iterable[Path] = (),
) -> list[str]:
    """Reuse main-root full-make .vo files for any run, excluding the current case."""

    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    excluded = {Path(path.as_posix()).with_suffix(".vo") for path in excluded_sources}
    reused: list[str] = []
    for _flag, physical, _logical in FIXED_LOAD_PATH_MAPPINGS:
        source_root = workspace_root / physical
        if not source_root.is_dir():
            continue
        for source in source_root.rglob("*.vo"):
            relative = source.relative_to(workspace_root)
            if relative in excluded:
                continue
            _reuse_one_base_vo(source, build_workspace / relative)
            reused.append(relative.as_posix())
    return sorted(set(reused))


def remove_target_case_side_products(build_workspace: Path, current_case_sources: Iterable[Path]) -> list[str]:
    """Remove stale target-case outputs before compiling current sources."""

    removed: list[str] = []
    for relative in current_case_sources:
        source = build_workspace / relative
        candidates = [source.with_suffix(suffix) for suffix in COQ_SIDE_PRODUCT_SUFFIXES]
        candidates.append(source.parent / f".{source.stem}.aux")
        for candidate in candidates:
            if candidate.exists() or candidate.is_symlink():
                candidate.unlink()
                removed.append(candidate.relative_to(build_workspace).as_posix())
    return sorted(set(removed))


def _strip_comments(text: str) -> str:
    previous = None
    current = text
    while previous != current:
        previous = current
        current = COMMENT_RE.sub("", current)
    return current


def _required_modules(text: str) -> list[str]:
    result: list[str] = []
    tokens = _strip_comments(text).replace("\n", " ").split()
    index = 0
    while index < len(tokens):
        prefix: str | None = None
        if tokens[index] == "From" and index + 2 < len(tokens) and tokens[index + 2] == "Require":
            prefix = tokens[index + 1].strip(".")
            index += 3
        elif tokens[index] == "Require":
            index += 1
        else:
            index += 1
            continue
        while index < len(tokens) and tokens[index] in {"Import", "Export"}:
            index += 1
        while index < len(tokens):
            token = tokens[index].strip()
            index += 1
            done = token.endswith(".")
            token = token.rstrip(".")
            if token and token not in {"as", "using"}:
                module = f"{prefix}.{token}" if prefix else token
                if module and module not in result:
                    result.append(module)
            if done:
                break
    return result


def logical_module_to_relative(module: str) -> Path | None:
    if module.startswith(STANDARD_PREFIXES):
        return None
    matches: list[tuple[int, Path, str]] = []
    for _flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS:
        if module == logical:
            matches.append((len(logical), Path(physical + ".v"), logical))
        elif module.startswith(logical + "."):
            suffix = module[len(logical) + 1 :].replace(".", "/") + ".v"
            matches.append((len(logical), Path(physical) / suffix, logical))
    if not matches:
        return None
    matches.sort(reverse=True, key=lambda item: item[0])
    return matches[0][1]


def relative_to_logical_module(rel: Path) -> str | None:
    rel = Path(rel.as_posix())
    matches: list[tuple[int, str]] = []
    for _flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS:
        physical_path = Path(physical)
        try:
            suffix = rel.relative_to(physical_path)
        except ValueError:
            continue
        if suffix.suffix != ".v":
            continue
        module_suffix = ".".join(suffix.with_suffix("").parts)
        module = f"{logical}.{module_suffix}" if module_suffix else logical
        matches.append((len(physical_path.parts), module))
    if not matches:
        return None
    matches.sort(reverse=True, key=lambda item: item[0])
    return matches[0][1]


def _local_alias_wrapper(build_workspace: Path, current_rel: Path, module: str) -> Path | None:
    if "." in module or module.startswith(STANDARD_PREFIXES):
        return None
    sibling = current_rel.parent / f"{module}.v"
    if not (build_workspace / sibling).is_file():
        return None
    logical = relative_to_logical_module(sibling)
    if logical is None:
        return None
    wrapper = Path(f"{module}.v")
    wrapper_path = build_workspace / wrapper
    wrapper_text = f"Require Export {logical}.\n"
    if not wrapper_path.exists() or wrapper_path.read_text(encoding="utf-8") != wrapper_text:
        wrapper_path.write_text(wrapper_text, encoding="utf-8")
    return wrapper


def _run(
    argv: list[str],
    *,
    cwd: Path,
    timeout_seconds: int | None = None,
    sigkill_retries: int = 0,
) -> dict[str, Any]:
    started = time.time()
    attempts = 0
    retry_returncodes: list[int] = []
    while True:
        attempts += 1
        try:
            proc = subprocess.run(
                argv,
                cwd=cwd,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout_seconds,
                check=False,
            )
            stdout = proc.stdout
            stderr = proc.stderr
            returncode = proc.returncode
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout if isinstance(exc.stdout, str) else ""
            stderr = exc.stderr if isinstance(exc.stderr, str) else ""
            stderr += f"\nCoq command timed out after {timeout_seconds} seconds."
            returncode = 124
        except FileNotFoundError as exc:
            stdout = ""
            stderr = str(exc)
            returncode = 127
        if returncode == -9 and attempts <= sigkill_retries:
            retry_returncodes.append(returncode)
            continue
        break
    combined = "\n".join(part for part in [stdout, stderr] if part)
    return {
        "argv": argv,
        "cwd": str(cwd),
        "returncode": returncode,
        "attempts": attempts,
        "sigkill_retries_configured": sigkill_retries,
        "transient_retry_returncodes": retry_returncodes,
        "stdout_tail": tail(stdout),
        "stderr_tail": tail(stderr),
        "first_diagnostic": extract_first_coq_diagnostic(combined),
        "elapsed_seconds": round(time.time() - started, 3),
    }


def _compile_order(
    build_workspace: Path,
    target_rel: Path,
    *,
    current_case_sources: Iterable[Path] = (),
) -> tuple[list[Path], list[str]]:
    ordered: list[Path] = []
    errors: list[str] = []
    visiting: set[Path] = set()
    visited: set[Path] = set()
    current_sources = {Path(path.as_posix()) for path in current_case_sources}

    def visit(rel: Path) -> None:
        rel = Path(rel.as_posix())
        if rel in visited:
            return
        if rel in visiting:
            errors.append(f"dependency cycle involving {rel.as_posix()}")
            return
        path = build_workspace / rel
        if not path.is_file():
            errors.append(f"missing Coq source in build workspace: {rel.as_posix()}")
            return
        visiting.add(rel)
        for module in _required_modules(path.read_text(encoding="utf-8")):
            dep = logical_module_to_relative(module)
            if dep is None:
                dep = _local_alias_wrapper(build_workspace, rel, module)
            if dep is not None and (build_workspace / dep).is_file():
                if dep in current_sources or not (build_workspace / dep.with_suffix(".vo")).is_file():
                    if dep not in current_sources and dep.parent != Path("."):
                        errors.append(
                            "missing trusted base .vo from the prerequisite full make: "
                            + dep.with_suffix(".vo").as_posix()
                        )
                    else:
                        visit(dep)
        visiting.remove(rel)
        visited.add(rel)
        ordered.append(rel)

    visit(target_rel)
    return ordered, errors


def _write_group_check_wrapper(build_workspace: Path, target_rel: Path, group_check: dict[str, Any]) -> None:
    case_theory = str(group_check.get("case_theory") or "").strip()
    require_modules = [str(item).strip() for item in group_check.get("require_modules", []) if str(item).strip()]
    assigned = [str(item).strip() for item in group_check.get("assigned_witnesses", []) if str(item).strip()]
    if not case_theory:
        raise ValueError("group-check requires case_theory")
    if not require_modules:
        raise ValueError("group-check requires require_modules")
    if not assigned:
        raise ValueError("group-check requires assigned_witnesses")
    lines = [
        "(* Generated build-workspace-only group check wrapper. *)",
        f"From {case_theory} Require Import {' '.join(require_modules)}.",
        "",
    ]
    lines.extend(f"Check {name}." for name in assigned)
    path = build_workspace / target_rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _compact_coq_result(evidence: dict[str, Any]) -> dict[str, Any]:
    result = {
        "schema_version": "qcp-coqc-check-result/v3",
        **{
            key: evidence.get(key)
            for key in (
                "status",
                "returncode",
                "target_file",
                "target_kind",
                "source_goal_version",
                "configured_coqc",
                "build_workspace",
                "overlaid_sources",
                "reused_base_vo_count",
                "recompiled_target_files",
                "first_diagnostic",
                "elapsed_seconds",
            )
            if evidence.get(key) is not None
        },
    }
    if evidence.get("status") != "passed":
        for key in ("failed_target_file", "dependency_errors", "stdout_tail", "stderr_tail"):
            if evidence.get(key):
                result[key] = evidence[key]
    return result


def run_coqc_check(
    *,
    workspace_root: Path,
    build_workspace: Path,
    target_file: Path,
    target_kind: str,
    source_goal_version: str | None,
    timeout_seconds: int | None = None,
    compile_dependencies: bool = True,
    group_check: dict[str, Any] | None = None,
    overlays: dict[Path, Path] | None = None,
) -> dict[str, Any]:
    started = time.time()
    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    target_rel = Path(target_file.as_posix())
    coqc_argv = make_coqc_argv(target_rel, workspace_root=workspace_root)
    layout_error = build_workspace_layout_error(workspace_root, build_workspace)
    if layout_error:
        return _compact_coq_result({
            "status": "failed",
            "tool": "coqc",
            "kind": "coqc_check",
            "argv": coqc_argv,
            "cwd": str(build_workspace),
            "configured_coqc": coqc_argv[0],
            "target_file": target_rel.as_posix(),
            "target_kind": target_kind,
            "source_goal_version": source_goal_version,
            "mirrored_sources_count": 0,
            "reused_base_vo_count": 0,
            "build_workspace": str(build_workspace),
            "dependency_order": [],
            "dependency_errors": [layout_error],
            "executed_argvs": [],
            "returncode": 2,
            "stdout_tail": "",
            "stderr_tail": layout_error,
            "first_diagnostic": None,
            "elapsed_seconds": round(time.time() - started, 3),
        })
    build_workspace.mkdir(parents=True, exist_ok=True)
    try:
        mirrored, overlaid = mirror_sources(
            workspace_root,
            build_workspace,
            [target_rel],
            overlays=overlays,
        )
    except ValueError as exc:
        return _compact_coq_result({
            "status": "failed",
            "tool": "coqc",
            "kind": "coqc_check",
            "argv": coqc_argv,
            "cwd": str(build_workspace),
            "configured_coqc": coqc_argv[0],
            "target_file": target_rel.as_posix(),
            "target_kind": target_kind,
            "source_goal_version": source_goal_version,
            "mirrored_sources_count": 0,
            "reused_base_vo_count": 0,
            "overlaid_sources": [],
            "build_workspace": str(build_workspace),
            "dependency_order": [],
            "dependency_errors": [str(exc)],
            "executed_argvs": [],
            "returncode": 2,
            "stdout_tail": "",
            "stderr_tail": str(exc),
            "first_diagnostic": None,
            "elapsed_seconds": round(time.time() - started, 3),
        })
    group_check_errors: list[str] = []
    if target_kind == "group-check":
        try:
            _write_group_check_wrapper(build_workspace, target_rel, group_check or {})
        except ValueError as exc:
            group_check_errors.append(str(exc))
    current_case_sources = target_case_sources(target_rel, group_check=group_check, overlays=overlays)
    remove_target_case_side_products(build_workspace, current_case_sources)
    reused_base_vo = reuse_base_vo_files(
        workspace_root,
        build_workspace,
        excluded_sources=current_case_sources,
    )
    order, dependency_errors = _compile_order(
        build_workspace,
        target_rel,
        current_case_sources=current_case_sources,
    )
    if not compile_dependencies:
        order = [target_rel]
    target_argv = make_coqc_argv(target_rel, workspace_root=workspace_root)
    sigkill_retries = coqc_transient_retries()
    evidence: dict[str, Any] = {
        "status": "pending",
        "tool": "coqc",
        "kind": "coqc_check",
        "argv": target_argv,
        "cwd": str(build_workspace),
        "configured_coqc": target_argv[0],
        "target_file": target_rel.as_posix(),
        "target_kind": target_kind,
        "source_goal_version": source_goal_version,
        "mirrored_sources_count": len(mirrored),
        "reused_base_vo_count": len(reused_base_vo),
        "overlaid_sources": overlaid,
        "coqc_transient_retry_policy": {
            "env": "COQC_TRANSIENT_RETRIES",
            "configured_retries": sigkill_retries,
            "retry_returncode": -9,
            "retry_signal": "SIGKILL",
        },
        "build_workspace": str(build_workspace),
        "dependency_order": [rel.as_posix() for rel in order],
        "recompiled_target_files": [rel.as_posix() for rel in order if rel in set(current_case_sources)],
        "dependency_errors": dependency_errors + group_check_errors,
        "executed_argvs": [],
        "returncode": None,
        "stdout_tail": "",
        "stderr_tail": "",
        "first_diagnostic": None,
    }
    if dependency_errors or group_check_errors:
        evidence["status"] = "failed"
        evidence["stderr_tail"] = "\n".join(dependency_errors + group_check_errors)
        evidence["elapsed_seconds"] = round(time.time() - started, 3)
        return _compact_coq_result(evidence)

    for rel in order:
        argv = make_coqc_argv(rel, workspace_root=workspace_root)
        result = _run(
            argv,
            cwd=build_workspace,
            timeout_seconds=timeout_seconds,
            sigkill_retries=sigkill_retries,
        )
        evidence["executed_argvs"].append(argv)
        if result["returncode"] != 0:
            evidence.update(
                {
                    "status": "failed",
                    "failed_target_file": rel.as_posix(),
                    "returncode": result["returncode"],
                    "stdout_tail": result["stdout_tail"],
                    "stderr_tail": result["stderr_tail"],
                    "first_diagnostic": result["first_diagnostic"],
                    "elapsed_seconds": round(time.time() - started, 3),
                }
            )
            return _compact_coq_result(evidence)
    evidence.update(
        {
            "status": "passed",
            "returncode": 0,
            "failed_target_file": None,
            "elapsed_seconds": round(time.time() - started, 3),
        }
    )
    return _compact_coq_result(evidence)


def run_coqtop_debug(
    *,
    workspace_root: Path,
    build_workspace: Path,
    debug_script: Path,
    source_goal_version: str | None,
    timeout_seconds: int | None = None,
    overlays: dict[Path, Path] | None = None,
) -> dict[str, Any]:
    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    debug_rel = Path(debug_script.as_posix())
    coqtop_argv = make_coqtop_argv(build_workspace / debug_rel, workspace_root=workspace_root)
    layout_error = build_workspace_layout_error(workspace_root, build_workspace)
    if layout_error:
        return {
            "schema_version": "qcp-coqtop-debug-evidence/v2",
            "status": "failed",
            "tool": "coqtop",
            "kind": "coqtop_debug",
            "argv": coqtop_argv,
            "cwd": str(build_workspace),
            "configured_coqtop": coqtop_argv[0],
            "debug_script": debug_rel.as_posix(),
            "source_goal_version": source_goal_version,
            "reused_base_vo_count": 0,
            "returncode": 2,
            "stdout_tail": "",
            "stderr_tail": layout_error,
            "first_diagnostic": None,
            "elapsed_seconds": 0.0,
        }
    build_workspace.mkdir(parents=True, exist_ok=True)
    try:
        _mirrored, overlaid = mirror_sources(
            workspace_root,
            build_workspace,
            [debug_rel],
            overlays=overlays,
        )
    except ValueError as exc:
        return {
            "schema_version": "qcp-coqtop-debug-evidence/v2",
            "status": "failed",
            "tool": "coqtop",
            "kind": "coqtop_debug",
            "argv": coqtop_argv,
            "cwd": str(build_workspace),
            "configured_coqtop": coqtop_argv[0],
            "debug_script": debug_rel.as_posix(),
            "source_goal_version": source_goal_version,
            "reused_base_vo_count": 0,
            "overlaid_sources": [],
            "returncode": 2,
            "stdout_tail": "",
            "stderr_tail": str(exc),
            "first_diagnostic": None,
            "elapsed_seconds": 0.0,
        }
    current_case_sources = target_case_sources(debug_rel, overlays=overlays)
    reused_base_vo = reuse_base_vo_files(
        workspace_root,
        build_workspace,
        excluded_sources=current_case_sources,
    )
    if not (build_workspace / debug_rel).is_file():
        return {
            "schema_version": "qcp-coqtop-debug-evidence/v2",
            "status": "failed",
            "tool": "coqtop",
            "kind": "coqtop_debug",
            "argv": coqtop_argv,
            "cwd": str(build_workspace),
            "configured_coqtop": coqtop_argv[0],
            "debug_script": debug_rel.as_posix(),
            "source_goal_version": source_goal_version,
            "reused_base_vo_count": len(reused_base_vo),
            "overlaid_sources": overlaid,
            "returncode": 2,
            "stdout_tail": "",
            "stderr_tail": f"debug script is missing from build workspace: {debug_rel}",
            "first_diagnostic": None,
            "elapsed_seconds": 0.0,
        }
    argv = make_coqtop_argv(build_workspace / debug_rel, workspace_root=workspace_root)
    result = _run(argv, cwd=build_workspace, timeout_seconds=timeout_seconds)
    return {
        "schema_version": "qcp-coqtop-debug-evidence/v2",
        "status": "passed" if result["returncode"] == 0 else "failed",
        "tool": "coqtop",
        "kind": "coqtop_debug",
        "argv": argv,
        "cwd": str(build_workspace),
        "configured_coqtop": argv[0],
        "debug_script": debug_rel.as_posix(),
        "source_goal_version": source_goal_version,
        "reused_base_vo_count": len(reused_base_vo),
        "overlaid_sources": overlaid,
        **result,
    }
