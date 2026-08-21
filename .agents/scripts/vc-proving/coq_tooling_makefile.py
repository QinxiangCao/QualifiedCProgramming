#!/usr/bin/env python3
"""Lock-free Makefile-backed Rocq tooling for the verification controller.

Dependency discovery occurs only at the same bounded preparation points used
by the Dune workflow.  One breadth-batched ``coqdep`` closure is rendered into
an exact run-local Makefile, GNU Make refreshes only that trusted-base closure,
and the resulting sources/artifacts/edges are sealed in a snapshot.  Proof,
debug, parent, and final checks consume that snapshot and never invoke another
dependency resolver or an aggregate repository Make target.
"""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import stat
import subprocess
import tempfile
import time
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from atomic_file import atomic_copy_file, atomic_write_text
from file_integrity import sha256_bytes, sha256_text
from file_integrity import sha256_file as file_sha256
from path_utils import (
    RUN_MAKEFILE_NAME,
    fixed_path_under,
    path_is_link_like,
    run_root_from_path,
)
from process_adapter import run_bounded_process


COQ_COMMAND_TIMEOUT_SECONDS = 1800
DUNE_BUILD_TIMEOUT_SECONDS = 1800
MAKEFILE_BUILD_TIMEOUT_SECONDS = DUNE_BUILD_TIMEOUT_SECONDS
MAKEFILE_BUILD_MODE = "makefile"
MAKEFILE_BUILD_DIRECTORY = Path(".")
MAKEFILE_SNAPSHOT_SCHEMA_VERSION = 1
MAKEFILE_SNAPSHOT_FILE_NAME = "makefile_dependency_snapshot.json"
DEPENDENCY_SNAPSHOT_FILE_NAME = MAKEFILE_SNAPSHOT_FILE_NAME
TARGETED_MAKE_GOAL = "trusted-base"

FIXED_LOAD_PATH_MAPPINGS: tuple[tuple[str, str, str], ...] = (
    ("-R", "Rocq/flocq/src", "Flocq"),
    ("-R", "Rocq/SeparationLogic", "SimpleC.SL"),
    ("-R", "Rocq/unifysl", "Logic"),
    ("-R", "Rocq/sets", "SetsClass"),
    ("-R", "Rocq/compcert_lib", "compcert.lib"),
    ("-R", "Rocq/auxlibs", "AUXLib"),
    ("-R", "Rocq/examples", "SimpleC.EE"),
    ("-R", "Rocq/stdlib", "SimpleC.StdLib"),
    ("-R", "Rocq/StrategyLib", "SimpleC.StrategyLib"),
    ("-R", "Rocq/Common", "SimpleC.Common"),
    ("-R", "Rocq/fixedpoints", "FP"),
    ("-R", "Rocq/MonadLib", "MonadLib"),
    ("-R", "Rocq/listlib", "ListLib"),
    ("-R", "Rocq/MaxMinLib", "MaxMinLib"),
    ("-R", "Rocq/GraphLib", "GraphLib"),
    ("-R", "Rocq/SumLib", "SumLib"),
    ("-R", "Rocq/tracelib", "TraceLib"),
    ("-R", "Rocq/coq-record-update/src", "RecordUpdate"),
    ("-Q", "Rocq/algorithms", "Algorithms"),
)

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
STANDARD_PREFIXES = ("Coq", "Ltac2")
STANDARD_MODULES = frozenset({"Nat", "Permutation", "String"})
PROOF_DECLARATION_RE = re.compile(
    r"^(Lemma|Theorem|Proposition|Corollary|Example|Fact|Remark)\s+"
    r"([A-Za-z0-9_']+)\s*:",
    re.MULTILINE,
)
PROOF_BLOCK_RE = re.compile(
    r"(?ms)^(?:Lemma|Theorem|Proposition|Corollary|Example|Fact|Remark)\s+"
    r"([A-Za-z0-9_']+)\s*:.*?\b(?:Qed|Defined|Admitted|Abort)\s*\.\s*"
)
COQ_FAILURE_RE = re.compile(
    r'File "(?P<file>[^"]+)", line (?P<line>\d+), characters '
    r"(?P<characters>[0-9-]+):\s*\n(?P<message>.*?)(?=\nFile \"|\Z)",
    re.DOTALL,
)
MAKE_ASSIGNMENT_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*(\?=|:=|=)\s*(.*?)\s*$"
)
MAKE_VARIABLE_RE = re.compile(r"\$\(([^()]+)\)|\$\{([^{}]+)\}")


@dataclass(frozen=True)
class CoqLoadPathEntry:
    flag: str
    physical: Path
    logical: str


class CoqBuildPlanError(ValueError):
    """Compact structured failure raised before a Rocq process starts."""

    def __init__(
        self,
        *,
        category: str,
        kind: str,
        message: str,
        repair: str,
        evidence: Mapping[str, Any] | None = None,
    ) -> None:
        super().__init__(message)
        self.category = category
        self.kind = kind
        self.repair = repair
        self.evidence = dict(evidence or {})

    def first_failure(self) -> dict[str, Any]:
        result: dict[str, Any] = {
            "category": self.category,
            "kind": self.kind,
            "message": str(self),
            "repair": self.repair,
        }
        if self.evidence:
            result["evidence"] = self.evidence
        return result


def tail(text: str, limit: int = 8000) -> str:
    return text if len(text) <= limit else text[-limit:]


def extract_first_coq_failure(output: str) -> dict[str, Any] | None:
    match = COQ_FAILURE_RE.search(output)
    if match is None:
        return None
    return {
        "file": match.group("file"),
        "line": int(match.group("line")),
        "characters": match.group("characters"),
        "message": match.group("message").strip(),
    }


def _stable_digest(value: Any) -> str:
    return sha256_text(
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    )


def _repository_relative(path: Path, root: Path, *, label: str) -> Path:
    raw = Path(path.as_posix())
    if raw.is_absolute():
        try:
            raw = path.expanduser().resolve().relative_to(root.expanduser().resolve())
        except ValueError as exc:
            raise CoqBuildPlanError(
                category="contract",
                kind="path-boundary",
                message=f"{label} escaped the repository: {path}",
                repair="Use the controller-persisted repository-relative target path.",
            ) from exc
    if ".." in raw.parts:
        raise CoqBuildPlanError(
            category="contract",
            kind="path-boundary",
            message=f"{label} is not a normalized repository-relative path: {raw}",
            repair="Use the controller-persisted repository-relative target path.",
        )
    return raw


def _regular_file(path: Path, *, label: str) -> Path:
    try:
        metadata = path.lstat()
    except FileNotFoundError as exc:
        raise CoqBuildPlanError(
            category="tooling",
            kind="missing-file",
            message=f"{label} is missing: {path}",
            repair="Restore the fixed regular file and rerun the unchanged command.",
        ) from exc
    if path_is_link_like(path) or not stat.S_ISREG(metadata.st_mode):
        raise CoqBuildPlanError(
            category="contract",
            kind="path-boundary",
            message=f"{label} must be a fixed non-link regular file: {path}",
            repair="Restore the fixed regular file without symlink or reparse indirection.",
        )
    return path


def _fixed_repository_path(root: Path, relative: Path, *, label: str) -> Path:
    try:
        return fixed_path_under(root / relative, root, label=label)
    except SystemExit as exc:
        raise CoqBuildPlanError(
            category="contract",
            kind="path-boundary",
            message=str(exc),
            repair="Restore a fixed non-link path inside the repository.",
        ) from exc


def _fixed_repository_file(root: Path, relative: Path, *, label: str) -> Path:
    return _regular_file(
        _fixed_repository_path(root, relative, label=label),
        label=label,
    )


def _optional_regular_file_digest(path: Path, *, label: str) -> str | None:
    """Hash an existing artifact without ever following path indirection."""

    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return None
    if path_is_link_like(path) or not stat.S_ISREG(metadata.st_mode):
        raise CoqBuildPlanError(
            category="contract",
            kind="path-boundary",
            message=f"{label} must be absent or a fixed non-link regular file: {path}",
            repair="Remove the path indirection and rerun the unchanged action.",
        )
    return file_sha256(path)


def _make_configuration_values(root: Path) -> dict[str, str]:
    """Read the small executable-selection subset of ``Rocq/CONFIGURE``."""

    path = _fixed_repository_path(
        root, Path("Rocq/CONFIGURE"), label="Makefile build configuration"
    )
    try:
        path.lstat()
    except FileNotFoundError:
        return {}
    _regular_file(path, label="Makefile build configuration")
    values: dict[str, str] = {}
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


def _expand_make_value(value: str, values: Mapping[str, str]) -> str:
    expanded = value
    for _index in range(20):
        replaced = MAKE_VARIABLE_RE.sub(
            lambda match: values.get(match.group(1) or match.group(2), ""),
            expanded,
        )
        if replaced == expanded:
            return replaced.strip()
        expanded = replaced
    raise CoqBuildPlanError(
        category="tooling",
        kind="makefile-configuration-recursion",
        message=f"recursive Makefile variable while resolving a tool: {value}",
        repair="Repair Rocq/CONFIGURE and rerun the unchanged action.",
    )


def _configured_program(root: Path, tool: str) -> str:
    environment_names = {
        "coqc": "COQC_EXE",
        "coqtop": "COQTOP_EXE",
        "coqdep": "COQDEP_EXE",
        "make": "MAKE_EXE",
    }
    environment_value = os.environ.get(environment_names[tool], "").strip()
    if environment_value:
        return environment_value
    if tool != "make":
        values = _make_configuration_values(root)
        defaults = {
            "coqc": ("COQC", "$(COQBIN)coqc$(SUF)"),
            "coqtop": ("COQTOP", "$(COQBIN)coqtop$(SUF)"),
            "coqdep": ("COQDEP", "$(COQBIN)coqdep$(SUF)"),
        }
        variable, fallback = defaults[tool]
        configured = _expand_make_value(values.get(variable, fallback), values)
        if configured:
            discovered = shutil.which(configured)
            return discovered or configured
    discovered = shutil.which(tool)
    if discovered:
        return discovered
    if tool == "make" and os.name == "nt":
        mingw_make = shutil.which("mingw32-make")
        if mingw_make:
            return mingw_make
    return tool


def configured_coq_executable(workspace_root: Path, tool: str) -> str:
    if tool not in {"coqc", "coqtop", "coqdep"}:
        raise ValueError(f"unsupported Rocq tool: {tool}")
    return _configured_program(workspace_root.expanduser().resolve(), tool)


def configured_make_executable(workspace_root: Path) -> str:
    return _configured_program(workspace_root.expanduser().resolve(), "make")


def _same_executable_path(left: str, right: str) -> bool:
    return os.path.normcase(os.path.normpath(left)) == os.path.normcase(
        os.path.normpath(right)
    )


def _base_load_path_entries(workspace_root: Path) -> tuple[CoqLoadPathEntry, ...]:
    root = workspace_root.expanduser().resolve()
    entries: list[CoqLoadPathEntry] = []
    for flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS:
        path = _fixed_repository_path(
            root, Path(physical), label="Makefile Rocq load-path root"
        )
        try:
            metadata = path.lstat()
        except FileNotFoundError as exc:
            raise CoqBuildPlanError(
                category="tooling",
                kind="load-path-plan-mismatch",
                message=f"Makefile Rocq load-path root is missing: {path}",
                repair="Restore the fixed Rocq source layout.",
            ) from exc
        if path_is_link_like(path) or not stat.S_ISDIR(metadata.st_mode):
            raise CoqBuildPlanError(
                category="contract",
                kind="load-path-plan-mismatch",
                message=f"Makefile Rocq load-path root is not a fixed directory: {path}",
                repair="Restore the fixed non-link Rocq source layout.",
            )
        entries.append(CoqLoadPathEntry(flag, path, logical))
    return tuple(entries)


def _render_load_path_flags(entries: Iterable[CoqLoadPathEntry]) -> list[str]:
    result: list[str] = []
    for entry in entries:
        if entry.flag not in {"-R", "-Q"} or not entry.physical.is_absolute():
            raise CoqBuildPlanError(
                category="contract",
                kind="load-path-plan-mismatch",
                message=f"invalid controller-owned Rocq load-path entry: {entry}",
                repair="Use the shared controller-owned load-path renderer.",
            )
        result.extend((entry.flag, str(entry.physical), entry.logical))
    return result


def _logical_root_for_relative(relative: Path) -> tuple[Path, str, str] | None:
    normalized = Path(relative.as_posix())
    for flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS:
        physical_root = Path(physical)
        try:
            nested = normalized.relative_to(physical_root)
        except ValueError:
            continue
        return physical_root, logical, flag
    return None


def logical_module_to_relative(module: str) -> Path | None:
    for _flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS:
        if module == logical:
            # A logical root is a theory prefix, not a physical source path.
            # A same-named unqualified module is resolved from the fixed
            # snapshot below (for example Rocq/sets/SetsClass.v).
            return None
        prefix = logical + "."
        if module.startswith(prefix):
            suffix = module[len(prefix) :].split(".")
            return Path(physical).joinpath(*suffix).with_suffix(".v")
    return None


def relative_to_logical_module(relative: Path) -> str | None:
    normalized = Path(relative.as_posix())
    mapping = _logical_root_for_relative(normalized)
    if mapping is None:
        return None
    physical, logical, _flag = mapping
    nested = normalized.relative_to(physical).with_suffix("")
    suffix = ".".join(nested.parts)
    return logical if not suffix else f"{logical}.{suffix}"


def _canonical_target_case_identity(relative: Path) -> tuple[Path, str] | None:
    if relative.suffix != ".v":
        return None
    for suffix in TARGET_CASE_SUFFIXES:
        if relative.stem.endswith(suffix) and len(relative.stem) > len(suffix):
            return relative.parent, relative.stem[: -len(suffix)]
    return None


def target_case_identity(
    target_rel: Path,
    *,
    case_anchor: Path | None = None,
    group_check: Mapping[str, Any] | None = None,
    overlays: Mapping[Path, Path] | None = None,
) -> tuple[Path, str] | None:
    identities: set[tuple[Path, str]] = set()
    for candidate in (
        [case_anchor] if case_anchor is not None else [target_rel]
    ) + list((overlays or {}).keys()):
        if candidate is None:
            continue
        identity = _canonical_target_case_identity(Path(candidate.as_posix()))
        if identity is not None:
            identities.add(identity)
    config = group_check or {}
    case_name = str(config.get("case_name") or "").strip()
    case_theory = str(config.get("case_theory") or "").strip()
    if case_name and case_theory:
        marker = logical_module_to_relative(case_theory + ".__qcp_marker__")
        if marker is not None:
            identities.add((marker.parent, case_name))
    if len(identities) != 1:
        return None
    identity = next(iter(identities))
    if case_name and identity[1] != case_name:
        return None
    return identity


def target_case_sources(
    target_rel: Path,
    *,
    case_anchor: Path | None = None,
    group_check: Mapping[str, Any] | None = None,
    overlays: Mapping[Path, Path] | None = None,
) -> list[Path]:
    identity = target_case_identity(
        target_rel,
        case_anchor=case_anchor,
        group_check=group_check,
        overlays=overlays,
    )
    if identity is None:
        return []
    directory, case_name = identity
    return [directory / f"{case_name}{suffix}" for suffix in TARGET_CASE_MODULE_SUFFIXES]


def build_workspace_layout_error(
    workspace_root: Path, build_workspace: Path
) -> str | None:
    root = workspace_root.expanduser().resolve()
    build = Path(os.path.abspath(os.fspath(build_workspace.expanduser())))
    run_root = run_root_from_path(build, root)
    if run_root is None:
        return (
            "build workspace must be under "
            "<main-root>/verification_runs/<run>/_coq_builds/...; got "
            + str(build)
        )
    expected = run_root / "_coq_builds"
    try:
        build.relative_to(expected)
    except ValueError:
        return f"build workspace escaped its run _coq_builds directory: {build}"
    current = expected
    for part in build.relative_to(expected).parts:
        current = current / part
        if current.exists() or current.is_symlink():
            if path_is_link_like(current) or not current.is_dir():
                return f"Coq build workspace contains a non-directory child: {current}"
    return None


def _strip_comments_and_strings(text: str) -> str:
    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        character = text[index]
        if depth:
            if pair == "(*":
                depth += 1
                output.extend("  ")
                index += 2
            elif pair == "*)":
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if character == "\n" else " ")
                index += 1
            continue
        if in_string:
            if character == '"' and text[index : index + 2] == '""':
                output.extend("  ")
                index += 2
            elif character == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if character == "\n" else " ")
                index += 1
            continue
        if pair == "(*":
            depth = 1
            output.extend("  ")
            index += 2
        elif character == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(character)
            index += 1
    return "".join(output)


def _required_modules(text: str) -> list[str]:
    modules: list[str] = []
    command_re = re.compile(
        r"\bFrom\s+([A-Za-z_][A-Za-z0-9_'.]*)\s+Require\s+"
        r"(?:Import|Export)?\s*([^.]*)\."
        r"|\bRequire\s+(?:Import|Export)?\s*([^.]*)\.",
        re.MULTILINE,
    )
    for match in command_re.finditer(text):
        prefix = match.group(1)
        body = match.group(2) if prefix is not None else match.group(3)
        if body is None:
            continue
        for token in re.findall(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", body):
            modules.append(f"{prefix}.{token}" if prefix else token)
    return modules


def _dependency_modules(text: str, *, source_label: Path) -> list[str]:
    code = _strip_comments_and_strings(text)
    unsupported = re.search(
        r"\b(?:Load|Add\s+(?:Rec\s+)?LoadPath|Remove\s+LoadPath|Cd)\b", code
    )
    if unsupported is not None:
        raise CoqBuildPlanError(
            category="tooling",
            kind="unsupported-current-case-dependency-form",
            message=(
                f"unsupported dynamic Rocq command `{unsupported.group(0)}` in "
                f"{source_label.as_posix()}"
            ),
            repair="Replace dynamic load-path commands with ordinary Require commands.",
        )
    return _required_modules(code)


def _is_standard_module(module: str) -> bool:
    return module in STANDARD_MODULES or any(
        module == prefix or module.startswith(prefix + ".")
        for prefix in STANDARD_PREFIXES
    )


def _is_external_module(module: str) -> bool:
    """Recognize installed modules absent from the sealed project graph.

    Rocq accepts many standard-library modules in historical unqualified form,
    including ``Lia`` and ``ZArith``. Qualified project imports still have to
    resolve to an artifact in the accepted snapshot.
    """

    return _is_standard_module(module) or "." not in module


def _makefile_configuration_records(root: Path) -> list[dict[str, Any]]:
    """Seal the fixed Make/Rocq configuration, including explicit absence."""

    records: list[dict[str, Any]] = []
    for relative in (Path("Rocq/Makefile"), Path("Rocq/CONFIGURE")):
        candidate = _fixed_repository_path(
            root, relative, label="Makefile build configuration"
        )
        present = candidate.exists() or candidate.is_symlink()
        record: dict[str, Any] = {
            "relative_path": relative.as_posix(),
            "present": present,
        }
        if present:
            _regular_file(candidate, label="Makefile build configuration")
            record["sha256"] = file_sha256(candidate)
        records.append(record)
    if not records[0]["present"]:
        raise CoqBuildPlanError(
            category="tooling",
            kind="repository-makefile-missing",
            message="repository Rocq/Makefile is missing",
            repair="Restore Rocq/Makefile before using Makefile build mode.",
        )
    return records


def _current_case_source_side_products(
    root: Path, current_family: Sequence[Path]
) -> list[Path]:
    candidates: list[Path] = []
    for source in current_family:
        outputs = [
            source.with_suffix(suffix) for suffix in COQ_SIDE_PRODUCT_SUFFIXES
        ]
        outputs.extend(
            (
                source.with_suffix(".aux"),
                source.parent / f".{source.stem}.aux",
            )
        )
        for relative in outputs:
            candidate = _fixed_repository_path(
                root, relative, label="current-case source side product"
            )
            try:
                metadata = candidate.lstat()
            except FileNotFoundError:
                continue
            if path_is_link_like(candidate) or not stat.S_ISREG(metadata.st_mode):
                raise CoqBuildPlanError(
                    category="contract",
                    kind="current-side-product-boundary",
                    message=(
                        "current-case source side product is not a fixed regular "
                        f"file: {candidate}"
                    ),
                    repair="Remove the special path and rerun the unchanged action.",
                )
            candidates.append(candidate)
    return sorted(set(candidates), key=lambda item: item.as_posix())


def _clean_current_case_source_side_products(
    root: Path, current_family: Sequence[Path]
) -> dict[str, Any]:
    """Remove only exact current-family outputs before a Make-backed check."""

    candidates = _current_case_source_side_products(root, current_family)
    removed: list[str] = []
    for candidate in candidates:
        candidate.unlink()
        removed.append(candidate.relative_to(root).as_posix())
    return {
        "status": "passed",
        "removed_count": len(removed),
        "first_removed": removed[0] if removed else None,
    }


def _unescape_coqdep_path_token(token: str) -> str:
    """Undo the Make escape used for a Windows drive separator."""

    return re.sub(r"^([A-Za-z])\\:", r"\1:", token)


def _parse_coqdep_output(
    stdout: str,
    *,
    workspace_root: Path,
) -> dict[Path, tuple[Path, ...]]:
    """Parse one batched coqdep result into repository-relative source edges."""

    root = workspace_root.expanduser().resolve()
    graph: dict[Path, set[Path]] = {}
    normalized = stdout.replace("\\\r\n", " ").replace("\\\n", " ")
    for line in normalized.splitlines():
        delimiter = re.search(r":\s", line)
        if delimiter is None:
            continue
        try:
            targets = shlex.split(line[: delimiter.start()], posix=os.name != "nt")
            dependencies = shlex.split(
                line[delimiter.end() :], posix=os.name != "nt"
            )
        except ValueError as exc:
            raise CoqBuildPlanError(
                category="tooling",
                kind="dependency-resolver-output",
                message=f"cannot parse batched coqdep output: {exc}",
                repair="Repair the controller-owned coqdep integration.",
            ) from exc

        def source_relative(token: str) -> Path | None:
            if (
                len(token) >= 2
                and token[0] == token[-1]
                and token[0] in {'"', "'"}
            ):
                token = token[1:-1]
            # coqdep renders dependency rules as Makefile syntax.  Its Windows
            # output escapes the drive separator (``C\:\\...``), which is not
            # a valid absolute Windows path until the Make escape is removed.
            # Keep ordinary backslashes intact because they are path
            # separators, not escaping characters in this part of the token.
            token = _unescape_coqdep_path_token(token)
            candidate = Path(token).with_suffix(".v")
            absolute = (
                candidate.resolve()
                if candidate.is_absolute()
                else (root / candidate).resolve()
            )
            try:
                relative = absolute.relative_to(root)
            except ValueError as exc:
                raise CoqBuildPlanError(
                    category="contract",
                    kind="dependency-path-boundary",
                    message=f"coqdep dependency escaped the repository: {absolute}",
                    repair="Repair the imported module or fixed load-path mapping.",
                ) from exc
            if not any(
                relative.is_relative_to(Path(physical))
                for _flag, physical, _logical in FIXED_LOAD_PATH_MAPPINGS
            ):
                return None
            return relative

        source = next(
            (
                relative
                for token in targets
                if (relative := source_relative(token)) is not None
            ),
            None,
        )
        if source is None:
            continue
        graph.setdefault(source, set()).update(
            relative
            for token in dependencies
            if (relative := source_relative(token)) is not None
            and relative != source
        )
    return {
        source: tuple(sorted(dependencies, key=lambda item: item.as_posix()))
        for source, dependencies in sorted(
            graph.items(), key=lambda item: item[0].as_posix()
        )
    }


def _run_batched_coqdep(
    *,
    workspace_root: Path,
    sources: Sequence[Path],
    timeout_seconds: float,
) -> tuple[dict[Path, tuple[Path, ...]], dict[str, Any]]:
    """Resolve one frontier with a single coqdep process."""

    root = workspace_root.expanduser().resolve()
    unique_sources = tuple(
        sorted({Path(item.as_posix()) for item in sources}, key=lambda item: item.as_posix())
    )
    if not unique_sources:
        return {}, {"process_count": 0, "source_count": 0, "elapsed_seconds": 0.0}
    load_entries = _base_load_path_entries(root)
    for item in unique_sources:
        _fixed_repository_file(root, item, label="coqdep source")
    tokens = [
        *(
            token
            for entry in load_entries
            for token in (
                entry.flag,
                entry.physical.relative_to(root).as_posix(),
                entry.logical,
            )
        ),
        *(item.as_posix() for item in unique_sources),
    ]
    started = time.monotonic()
    descriptor, argument_name = tempfile.mkstemp(
        prefix=".qcp-coqdep-", suffix=".args", dir=root
    )
    arguments = Path(argument_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(
                " ".join(json.dumps(str(token)) for token in tokens) + "\n",
            )
            handle.flush()
            os.fsync(handle.fileno())
        argv = [
            configured_coq_executable(root, "coqdep"),
            "-f",
            str(arguments),
        ]
        process = run_bounded_process(
            argv,
            cwd=root,
            timeout_seconds=timeout_seconds,
            timeout_message=f"\ncoqdep timed out after {timeout_seconds:g} seconds.",
            detached_pipe_message="\ncoqdep cleanup could not fully drain a detached pipe.",
            launch_error_prefix="cannot launch coqdep: ",
        )
    finally:
        try:
            arguments.unlink()
        except FileNotFoundError:
            pass
    if process.returncode != 0:
        raise CoqBuildPlanError(
            category="tooling",
            kind="dependency-resolver-failed",
            message=tail(process.stderr or process.stdout) or "coqdep failed",
            repair="Repair the first dependency diagnostic and rerun preparation.",
        )
    return _parse_coqdep_output(process.stdout, workspace_root=root), {
        "process_count": 1,
        "source_count": len(unique_sources),
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def _resolve_exact_dependency_graph(
    *,
    workspace_root: Path,
    roots: Sequence[Path],
    timeout_seconds: float,
) -> tuple[dict[Path, tuple[Path, ...]], dict[str, Any]]:
    """Resolve the transitive closure in breadth batches, not once per node."""

    root = workspace_root.expanduser().resolve()
    started = time.monotonic()
    deadline = started + timeout_seconds
    pending = {Path(item.as_posix()) for item in roots}
    graph: dict[Path, tuple[Path, ...]] = {}
    process_count = 0
    resolved_source_count = 0
    batch_count = 0
    while pending:
        batch = tuple(sorted(pending - set(graph), key=lambda item: item.as_posix()))
        pending.clear()
        if not batch:
            break
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise CoqBuildPlanError(
                category="tooling",
                kind="dependency-resolver-timeout",
                message="dependency resolution exhausted the preparation deadline",
                repair="Repair the dependency graph and rerun preparation.",
            )
        batch_graph, metrics = _run_batched_coqdep(
            workspace_root=root,
            sources=batch,
            timeout_seconds=remaining,
        )
        process_count += int(metrics["process_count"])
        resolved_source_count += int(metrics["source_count"])
        batch_count += 1
        for source in batch:
            if source not in batch_graph:
                raise CoqBuildPlanError(
                    category="tooling",
                    kind="dependency-resolver-output",
                    message=f"coqdep omitted requested source: {source.as_posix()}",
                    repair="Repair the source/load-path configuration and rerun.",
                )
            dependencies = batch_graph[source]
            graph[source] = dependencies
            pending.update(dependency for dependency in dependencies if dependency not in graph)
    return graph, {
        "status": "resolved",
        "strategy": "breadth-batched-coqdep",
        "batch_count": batch_count,
        "coqdep_process_count": process_count,
        "node_count": len(graph),
        "source_count": resolved_source_count,
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def _dependency_closure(
    graph: Mapping[Path, Sequence[Path]], target: Path
) -> tuple[Path, ...]:
    visited: set[Path] = set()
    visiting: set[Path] = set()

    def visit(node: Path) -> None:
        if node in visited:
            return
        if node in visiting:
            raise CoqBuildPlanError(
                category="tooling",
                kind="makefile-dependency-cycle",
                message=f"coqdep data contains a cycle at {node.as_posix()}",
                repair="Repair the Rocq module dependency cycle and rerun preparation.",
            )
        visiting.add(node)
        for dependency in graph.get(node, ()):
            visit(dependency)
        visiting.remove(node)
        visited.add(node)

    visit(target)
    return tuple(sorted(visited, key=lambda item: item.as_posix()))


def _make_path_token(path: Path) -> str:
    value = Path(path.as_posix()).as_posix()
    unsupported = ("\n", "\r", "\0", "\t", "#", "$", "%", ";", "|", "*", "?", "[", "]")
    if any(character in value for character in unsupported) or ":" in value:
        raise CoqBuildPlanError(
            category="contract",
            kind="targeted-make-target-boundary",
            message=f"Makefile dependency path contains unsupported syntax: {value!r}",
            repair="Use normalized repository paths without Make metacharacters.",
        )
    return value.replace(" ", "\\ ")


def _recipe_command(tokens: Iterable[str]) -> str:
    rendered = [str(token) for token in tokens]
    command = subprocess.list2cmdline(rendered) if os.name == "nt" else shlex.join(rendered)
    return command.replace("$", "$$")


def _render_exact_makefile(
    *,
    workspace_root: Path,
    target_rel: Path,
    current_family: Sequence[Path],
    graph: Mapping[Path, Sequence[Path]],
    source_goal_version: str | None,
    configuration_records: Sequence[Mapping[str, Any]] | None = None,
) -> str:
    """Render one standalone Makefile for the exact trusted-base closure."""

    root = workspace_root.expanduser().resolve()
    if source_goal_version is not None and (
        not isinstance(source_goal_version, str)
        or any(character in source_goal_version for character in ("\n", "\r", "\0"))
    ):
        raise CoqBuildPlanError(
            category="contract",
            kind="targeted-make-target-boundary",
            message="source_goal_version contains unsupported Makefile text",
            repair="Use the controller-derived source_goal_version digest.",
        )
    closure = set(_dependency_closure(graph, target_rel))
    family = {Path(item.as_posix()) for item in current_family}
    base_sources = closure - family
    if target_rel not in family:
        raise CoqBuildPlanError(
            category="contract",
            kind="targeted-make-target-boundary",
            message="exact preparation target is outside the current-case family",
            repair="Use the persisted formal_case_lib or goal_check target.",
        )
    for source in base_sources:
        escaped = set(graph.get(source, ())) - base_sources
        if escaped:
            dependency = min(escaped, key=lambda item: item.as_posix())
            raise CoqBuildPlanError(
                category="contract",
                kind="trusted-base-depends-on-current-case",
                message=(
                    f"trusted-base source {source.as_posix()} depends on current "
                    f"or out-of-closure source {dependency.as_posix()}"
                ),
                repair="Repair the dependency direction before preparing the base.",
            )
    targets = [
        source.with_suffix(".vo")
        for source in sorted(base_sources, key=lambda item: item.as_posix())
    ]
    compiler = [
        configured_coq_executable(root, "coqc"),
        "-q",
        *_render_load_path_flags(_base_load_path_entries(root)),
    ]
    configuration_prerequisites = [
        Path(record["relative_path"])
        for record in (
            configuration_records
            if configuration_records is not None
            else _makefile_configuration_records(root)
        )
        if record["present"]
    ]
    lines = [
        "# Generated by the QCP verification controller.",
        f"# Source version: {source_goal_version or ''}",
        "# Exact trusted-base closure only; do not edit.",
        f".DEFAULT_GOAL := {TARGETED_MAKE_GOAL}",
        ".DELETE_ON_ERROR:",
        ".NOTPARALLEL:",
        ".SUFFIXES:",
    ]
    if os.name == "nt":
        lines.extend(("SHELL := cmd.exe", ".SHELLFLAGS := /d /s /c"))
    lines.extend(("", "BASE_CLOSURE_VO :=" + (" \\" if targets else "")))
    for index, target in enumerate(targets):
        continuation = " \\" if index + 1 < len(targets) else ""
        lines.append(f"  {_make_path_token(target)}{continuation}")
    lines.extend(
        [
            "",
            f".PHONY: {TARGETED_MAKE_GOAL}",
            f"{TARGETED_MAKE_GOAL}: $(BASE_CLOSURE_VO)",
            "",
        ]
    )
    for source in sorted(base_sources, key=lambda item: item.as_posix()):
        _fixed_repository_file(root, source, label="Makefile dependency source")
        prerequisites = [
            _make_path_token(source),
            *(
                _make_path_token(configuration)
                for configuration in configuration_prerequisites
            ),
            *(
                _make_path_token(dependency.with_suffix(".vo"))
                for dependency in sorted(
                    graph.get(source, ()), key=lambda item: item.as_posix()
                )
            ),
        ]
        lines.append(
            f"{_make_path_token(source.with_suffix('.vo'))}: "
            + " ".join(prerequisites)
        )
    if targets:
        lines.extend(
            [
                "",
                "$(BASE_CLOSURE_VO):",
                f"\t{_recipe_command(compiler)} \"$(@:.vo=.v)\"",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def _make_environment() -> dict[str, str]:
    environment = dict(os.environ)
    for name in (
        "MAKEFLAGS",
        "MFLAGS",
        "GNUMAKEFLAGS",
        "MAKELEVEL",
        "MAKEFILES",
        "MAKEOVERRIDES",
        "COQC",
        "COQDEP",
        "COQFLAGS",
        "COQPATH",
        "ROCQPATH",
    ):
        environment.pop(name, None)
    return environment


def _targeted_make_argv(workspace_root: Path, run_makefile: Path) -> list[str]:
    return [
        configured_make_executable(workspace_root),
        "--no-print-directory",
        "--no-builtin-rules",
        "--no-builtin-variables",
        "-f",
        str(run_makefile.expanduser().resolve()),
        TARGETED_MAKE_GOAL,
    ]


def validate_targeted_make_argv(
    *,
    workspace_root: Path,
    run_makefile: Path,
    argv: Iterable[str],
) -> list[str]:
    """Reject aggregate goals and any drift from the one exact Make action."""

    actual = [str(item) for item in argv]
    expected = _targeted_make_argv(workspace_root, run_makefile)
    forbidden = {"all", "core", "examples", "depend"}
    aggregate = next(
        (
            token
            for token in actual
            if token in forbidden or token.startswith("examples-")
        ),
        None,
    )
    if aggregate is not None:
        return [f"targeted-make-aggregate-forbidden: {aggregate}"]
    if actual != expected:
        return [
            (
                "targeted-make-target-boundary: Make argv must contain only the "
                "configured executable, one run-local exact Makefile, and the "
                f"explicit {TARGETED_MAKE_GOAL} goal"
            )
        ]
    return []


def _snapshot_payload(
    *,
    workspace_root: Path,
    target_rel: Path,
    case_identity: tuple[Path, str],
    current_family: Sequence[Path],
    source_goal_version: str | None,
    make_executable: str,
    run_makefile: Path,
    persist_makefile: bool,
    graph: Mapping[Path, Sequence[Path]],
    dependency_metrics: Mapping[str, Any],
    configuration: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    root = workspace_root.expanduser().resolve()
    closure_sources = _dependency_closure(graph, target_rel)
    family_sources = {Path(item.as_posix()) for item in current_family}
    current_sources = set(closure_sources) & family_sources
    base_sources = set(closure_sources) - family_sources

    artifact_records: list[dict[str, str]] = []
    source_records: list[dict[str, str]] = []
    for source in sorted(base_sources, key=lambda item: item.as_posix()):
        artifact = source.with_suffix(".vo")
        artifact_path = _fixed_repository_file(
            root, artifact, label="Makefile-prepared base artifact"
        )
        source_path = _fixed_repository_file(
            root, source, label="Makefile dependency source"
        )
        artifact_records.append(
            {"relative_path": artifact.as_posix(), "sha256": file_sha256(artifact_path)}
        )
        source_records.append(
            {"relative_path": source.as_posix(), "sha256": file_sha256(source_path)}
        )

    dependency_records = [
        {
            "artifact": source.with_suffix(".vo").as_posix(),
            "requires": [
                dependency.with_suffix(".vo").as_posix()
                for dependency in graph.get(source, ())
                if dependency in closure_sources
            ],
        }
        for source in closure_sources
    ]
    current_dependencies = [
        {
            "source": source.as_posix(),
            "requires": [
                dependency.as_posix()
                for dependency in graph.get(source, ())
                if dependency in current_sources
            ],
        }
        for source in sorted(current_sources, key=lambda item: item.as_posix())
    ]
    sealed_configuration = [dict(record) for record in configuration]
    directory, case_name = case_identity
    payload = {
        "schema_version": MAKEFILE_SNAPSHOT_SCHEMA_VERSION,
        "build_mode": MAKEFILE_BUILD_MODE,
        "source_goal_version": source_goal_version,
        "target": target_rel.with_suffix(".vo").as_posix(),
        "build_root": MAKEFILE_BUILD_DIRECTORY.as_posix(),
        "make_executable": make_executable,
        "coqc_executable": configured_coq_executable(root, "coqc"),
        "coqdep_executable": configured_coq_executable(root, "coqdep"),
        "run_makefile": (
            run_makefile.relative_to(root).as_posix() if persist_makefile else None
        ),
        "run_makefile_sha256": file_sha256(run_makefile),
        "case_directory": directory.as_posix(),
        "case_name": case_name,
        "current_family": [item.as_posix() for item in current_family],
        "current_sources": [
            item.as_posix()
            for item in sorted(current_sources, key=lambda value: value.as_posix())
        ],
        "current_dependencies": current_dependencies,
        "dependencies": dependency_records,
        "base_sources": source_records,
        "base_artifacts": artifact_records,
        "configuration": sealed_configuration,
        "dependency_metrics": dict(dependency_metrics),
    }
    payload["dependency_digest"] = _stable_digest(dependency_records)
    payload["source_digest"] = _stable_digest(source_records)
    payload["artifact_digest"] = _stable_digest(artifact_records)
    payload["configuration_digest"] = _stable_digest(sealed_configuration)
    return payload


def _dune_failure(
    *,
    target: Path,
    started: float,
    kind: str,
    message: str,
    repair: str,
    returncode: int = 2,
    **extra: Any,
) -> dict[str, Any]:
    return {
        "status": "failed",
        "build_mode": MAKEFILE_BUILD_MODE,
        "target": target.as_posix(),
        "returncode": returncode,
        "first_failure": {
            "category": "tooling",
            "kind": kind,
            "message": message,
            "repair": repair,
        },
        "elapsed_seconds": round(time.monotonic() - started, 6),
        **extra,
    }


def prepare_dune_dependencies(
    *,
    workspace_root: Path,
    target_file: Path,
    current_case_anchor: Path,
    source_goal_version: str | None,
    snapshot_path: Path | None = None,
    timeout_seconds: int | float | None = DUNE_BUILD_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Resolve once, run one exact Make goal, and seal its dependency snapshot."""

    started = time.monotonic()
    timeout = float(
        MAKEFILE_BUILD_TIMEOUT_SECONDS if timeout_seconds is None else timeout_seconds
    )
    root = workspace_root.expanduser().resolve()
    temporary: tempfile.TemporaryDirectory[str] | None = None
    try:
        target_rel = _repository_relative(target_file, root, label="Makefile target")
        anchor = _repository_relative(
            current_case_anchor, root, label="current-case anchor"
        )
        identity = target_case_identity(target_rel, case_anchor=anchor)
        if identity is None:
            raise CoqBuildPlanError(
                category="contract",
                kind="load-path-plan-mismatch",
                message="Makefile build lacks one authoritative current-case identity",
                repair="Restore the persisted target_files case anchor.",
            )
        family = target_case_sources(target_rel, case_anchor=anchor)
        if target_rel not in family:
            raise CoqBuildPlanError(
                category="contract",
                kind="makefile-target-boundary",
                message=f"Makefile target is outside the exact current family: {target_rel}",
                repair="Build only the persisted formal_case_lib or goal_check target.",
            )
        _fixed_repository_file(root, target_rel, label="Makefile target source")
        configuration_seal = _makefile_configuration_records(root)

        current_cleanup = _clean_current_case_source_side_products(root, family)

        graph, dependency_metrics = _resolve_exact_dependency_graph(
            workspace_root=root,
            roots=[target_rel],
            timeout_seconds=max(0.0, timeout - (time.monotonic() - started)),
        )
        closure = _dependency_closure(graph, target_rel)
        source_seal = {
            source: file_sha256(
                _fixed_repository_file(
                    root, source, label="resolved dependency source"
                )
            )
            for source in closure
        }
        family_set = {Path(item.as_posix()) for item in family}
        base_sources = set(closure) - family_set
        before_artifacts = {
            source.with_suffix(".vo"): _optional_regular_file_digest(
                _fixed_repository_path(
                    root,
                    source.with_suffix(".vo"),
                    label="existing Makefile base artifact",
                ),
                label="existing Makefile base artifact",
            )
            for source in base_sources
        }

        persist_makefile = snapshot_path is not None
        snapshot: Path | None = None
        if snapshot_path is not None:
            snapshot = fixed_path_under(
                snapshot_path,
                root,
                label="run Makefile dependency snapshot",
            )
            run_root = run_root_from_path(snapshot, root)
            if run_root is None or snapshot.parent != run_root:
                raise CoqBuildPlanError(
                    category="contract",
                    kind="makefile-snapshot-path",
                    message="accepted Makefile snapshot must be directly under its run root",
                    repair="Use verification_runs/<run>/makefile_dependency_snapshot.json.",
                )
            run_makefile = run_root / RUN_MAKEFILE_NAME
        else:
            temporary = tempfile.TemporaryDirectory(
                prefix=".qcp-exact-make-", dir=root
            )
            run_makefile = Path(temporary.name) / RUN_MAKEFILE_NAME

        run_makefile = _fixed_repository_path(
            root,
            run_makefile.relative_to(root),
            label="run-local exact Makefile",
        )
        try:
            run_makefile.lstat()
        except FileNotFoundError:
            pass
        else:
            _regular_file(run_makefile, label="run-local exact Makefile")

        makefile_text = _render_exact_makefile(
            workspace_root=root,
            target_rel=target_rel,
            current_family=family,
            graph=graph,
            source_goal_version=source_goal_version,
            configuration_records=configuration_seal,
        )
        atomic_write_text(run_makefile, makefile_text, suffix=".makefile")
        makefile_digest = file_sha256(run_makefile)
        make = configured_make_executable(root)
        argv = _targeted_make_argv(root, run_makefile)
        argv_errors = validate_targeted_make_argv(
            workspace_root=root,
            run_makefile=run_makefile,
            argv=argv,
        )
        if argv_errors:
            kind, message = argv_errors[0].split(": ", 1)
            raise CoqBuildPlanError(
                category="contract",
                kind=kind,
                message=message,
                repair=(
                    "Repair the controller-owned run-local Make argv; "
                    "do not broaden its goal."
                ),
            )
        remaining = timeout - (time.monotonic() - started)
        if remaining <= 0:
            raise CoqBuildPlanError(
                category="tooling",
                kind="targeted-make-timeout",
                message="dependency discovery exhausted the Makefile preparation deadline",
                repair="Repair the dependency graph and rerun the unchanged action.",
            )
        make_started = time.monotonic()
        process = run_bounded_process(
            argv,
            cwd=root,
            timeout_seconds=remaining,
            environment=_make_environment(),
            timeout_message=f"\nExact Make build timed out after {remaining:g} seconds.",
            detached_pipe_message="\nMake cleanup could not fully drain a detached pipe.",
            launch_error_prefix="cannot launch GNU Make: ",
        )
        make_seconds = round(time.monotonic() - make_started, 6)
        combined = "\n".join(item for item in (process.stdout, process.stderr) if item)
        if process.returncode != 0:
            return _dune_failure(
                target=target_rel,
                started=started,
                kind=(
                    "targeted-make-executable-unavailable"
                    if process.returncode == 127
                    else "targeted-make-failed"
                ),
                message=tail(process.stderr or process.stdout) or "GNU Make failed",
                repair="Repair the first Make/Rocq diagnostic and rerun the exact action.",
                returncode=process.returncode,
                build_mode=MAKEFILE_BUILD_MODE,
                argv=argv,
                stdout_tail=tail(process.stdout),
                stderr_tail=tail(process.stderr),
                first_diagnostic=extract_first_coq_failure(combined),
                makefile_digest=makefile_digest,
                dependency_metrics=dependency_metrics,
                current_cleanup=current_cleanup,
                make_seconds=make_seconds,
            )
        if file_sha256(run_makefile) != makefile_digest:
            raise CoqBuildPlanError(
                category="contract",
                kind="targeted-make-target-boundary",
                message="run-local exact Makefile changed during execution",
                repair="Restore the controller-owned Makefile and rerun preparation.",
            )
        for source, digest in source_seal.items():
            if file_sha256(
                _fixed_repository_file(
                    root, source, label="dependency source after Make"
                )
            ) != digest:
                raise CoqBuildPlanError(
                    category="freshness",
                    kind="makefile-source-drift",
                    message=f"dependency source changed during Make: {source.as_posix()}",
                    repair="Rerun preparation after repository sources stabilize.",
                )
        configuration_after = _makefile_configuration_records(root)
        if configuration_after != configuration_seal:
            raise CoqBuildPlanError(
                category="freshness",
                kind="makefile-configuration-drift",
                message="Makefile build configuration changed during preparation",
                repair="Rerun preparation after Makefile configuration stabilizes.",
            )

        payload = _snapshot_payload(
            workspace_root=root,
            target_rel=target_rel,
            case_identity=identity,
            current_family=family,
            source_goal_version=source_goal_version,
            make_executable=make,
            run_makefile=run_makefile,
            persist_makefile=persist_makefile,
            graph=graph,
            dependency_metrics=dependency_metrics,
            configuration=configuration_after,
        )
        rebuilt_count = sum(
            1
            for artifact, before in before_artifacts.items()
            if file_sha256(_regular_file(root / artifact, label="prepared base artifact"))
            != before
        )
        target_artifact = target_rel.with_suffix(".vo")
        receipt: dict[str, Any] = {
            "status": "passed",
            "build_mode": MAKEFILE_BUILD_MODE,
            "source_goal_version": source_goal_version,
            "target": target_artifact.as_posix(),
            "build_root": MAKEFILE_BUILD_DIRECTORY.as_posix(),
            "make_executable": make,
            "coqc_executable": payload["coqc_executable"],
            "coqdep_executable": payload["coqdep_executable"],
            "run_makefile": payload["run_makefile"],
            "run_makefile_sha256": makefile_digest,
            "dependency_digest": payload["dependency_digest"],
            "source_digest": payload["source_digest"],
            "artifact_digest": payload["artifact_digest"],
            "configuration_digest": payload["configuration_digest"],
            "base_artifact_count": len(payload["base_artifacts"]),
            "current_source_count": len(payload["current_sources"]),
            "rebuilt_count": rebuilt_count,
            "dependency_metrics": dependency_metrics,
            "current_cleanup": current_cleanup,
            "make_seconds": make_seconds,
            "returncode": 0,
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
        if snapshot is None:
            receipt["_snapshot"] = payload
        else:
            atomic_write_text(
                snapshot,
                json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
                suffix=".makefile-snapshot",
            )
            receipt["snapshot"] = snapshot.relative_to(root).as_posix()
            receipt["snapshot_sha256"] = file_sha256(snapshot)
        return receipt
    except CoqBuildPlanError as exc:
        return {
            "status": "failed",
            "build_mode": MAKEFILE_BUILD_MODE,
            "returncode": 2,
            "first_failure": exc.first_failure(),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return _dune_failure(
            target=Path(target_file.as_posix()),
            started=started,
            kind="makefile-preparation-failed",
            message=str(exc) or repr(exc),
            repair="Restore readable Makefile configuration, sources, and build output.",
            build_mode=MAKEFILE_BUILD_MODE,
        )
    finally:
        if temporary is not None:
            temporary.cleanup()


def compact_dune_preparation(evidence: Mapping[str, Any]) -> dict[str, Any]:
    keys = (
        "status",
        "build_mode",
        "source_goal_version",
        "target",
        "build_root",
        "make_executable",
        "coqc_executable",
        "coqdep_executable",
        "run_makefile",
        "run_makefile_sha256",
        "snapshot",
        "snapshot_sha256",
        "dependency_digest",
        "source_digest",
        "artifact_digest",
        "configuration_digest",
        "base_artifact_count",
        "current_source_count",
        "rebuilt_count",
        "dependency_metrics",
        "current_cleanup",
        "make_seconds",
        "returncode",
        "elapsed_seconds",
        "first_failure",
    )
    return {key: evidence[key] for key in keys if key in evidence}


def _snapshot_relative_path(
    value: Any,
    *,
    label: str,
    suffix: str | None = None,
) -> Path:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label} must be a non-empty repository-relative path")
    relative = Path(value)
    if (
        relative.is_absolute()
        or not relative.parts
        or ".." in relative.parts
        or "." in relative.parts
        or ":" in value
        or "\\" in value
        or relative.as_posix() != value
    ):
        raise ValueError(f"{label} is not a normalized repository-relative path")
    if suffix is not None and relative.suffix != suffix:
        raise ValueError(f"{label} must end in {suffix}")
    return relative


def _snapshot_digest(value: Any, *, label: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{label} is not a lowercase SHA-256 digest")
    return value


def _strict_snapshot(payload: Any) -> dict[str, Any]:
    if not isinstance(payload, dict):
        raise CoqBuildPlanError(
            category="contract",
            kind="makefile-snapshot-invalid",
            message="Makefile dependency snapshot is not a JSON object",
            repair="Rerun the controller-owned build-preparation action.",
        )
    required = {
        "schema_version",
        "build_mode",
        "source_goal_version",
        "target",
        "build_root",
        "make_executable",
        "coqc_executable",
        "coqdep_executable",
        "run_makefile",
        "run_makefile_sha256",
        "case_directory",
        "case_name",
        "current_family",
        "current_sources",
        "current_dependencies",
        "dependencies",
        "base_sources",
        "base_artifacts",
        "configuration",
        "dependency_metrics",
        "dependency_digest",
        "source_digest",
        "artifact_digest",
        "configuration_digest",
    }
    if (
        set(payload) != required
        or payload.get("schema_version") != MAKEFILE_SNAPSHOT_SCHEMA_VERSION
        or payload.get("build_mode") != MAKEFILE_BUILD_MODE
    ):
        raise CoqBuildPlanError(
            category="contract",
            kind="makefile-snapshot-invalid",
            message="Makefile dependency snapshot fields or schema version are invalid",
            repair="Rerun the controller-owned build-preparation action.",
        )
    return payload


def _load_snapshot_from_receipt(
    *, workspace_root: Path, receipt: Mapping[str, Any]
) -> dict[str, Any]:
    root = workspace_root.expanduser().resolve()
    embedded = receipt.get("_snapshot")
    if embedded is not None:
        return _strict_snapshot(embedded)
    try:
        relative = _snapshot_relative_path(
            receipt.get("snapshot"),
            label="Makefile preparation snapshot",
            suffix=".json",
        )
    except ValueError as exc:
        raise CoqBuildPlanError(
            category="contract",
            kind="makefile-snapshot-path",
            message=str(exc),
            repair="Rerun the controller-owned build-preparation action.",
        ) from exc
    path = fixed_path_under(root / relative, root, label="Makefile dependency snapshot")
    run_root = run_root_from_path(path, root)
    if (
        run_root is None
        or path.parent != run_root
        or path.name != MAKEFILE_SNAPSHOT_FILE_NAME
    ):
        raise CoqBuildPlanError(
            category="contract",
            kind="makefile-snapshot-path",
            message="Makefile dependency snapshot is not the fixed run-root path",
            repair="Use verification_runs/<run>/makefile_dependency_snapshot.json.",
        )
    _regular_file(path, label="Makefile dependency snapshot")
    try:
        expected_digest = _snapshot_digest(
            receipt.get("snapshot_sha256"), label="snapshot_sha256"
        )
    except ValueError as exc:
        raise CoqBuildPlanError(
            category="freshness",
            kind="makefile-snapshot-drift",
            message=str(exc),
            repair="Rerun the controller-owned build-preparation action.",
        ) from exc
    raw = path.read_bytes()
    if not expected_digest or sha256_bytes(raw) != expected_digest:
        raise CoqBuildPlanError(
            category="freshness",
            kind="makefile-snapshot-drift",
            message="Makefile dependency snapshot bytes changed after preparation",
            repair="Rerun the controller-owned build-preparation action.",
        )
    return _strict_snapshot(json.loads(raw.decode("utf-8")))


def _validated_dune_snapshot(
    *,
    workspace_root: Path,
    receipt: Mapping[str, Any] | None,
    expected_source_goal_version: str | None = None,
) -> dict[str, Any]:
    """Validate one receipt and return the exact snapshot already inspected."""

    root = workspace_root.expanduser().resolve()
    if (
        not isinstance(receipt, Mapping)
        or receipt.get("status") != "passed"
        or receipt.get("build_mode") != MAKEFILE_BUILD_MODE
    ):
        raise ValueError("accepted Makefile preparation is missing")
    snapshot = _load_snapshot_from_receipt(
        workspace_root=root, receipt=receipt
    )
    for field in (
        "source_goal_version",
        "target",
        "build_root",
        "make_executable",
        "coqc_executable",
        "coqdep_executable",
        "run_makefile",
        "run_makefile_sha256",
    ):
        if receipt.get(field) != snapshot.get(field):
            raise ValueError(f"Makefile preparation {field} is invalid")
    if (
        expected_source_goal_version is not None
        and snapshot.get("source_goal_version") != expected_source_goal_version
    ):
        raise ValueError("Makefile preparation source_goal_version is stale")
    for field in (
        "current_family",
        "current_sources",
        "current_dependencies",
        "dependencies",
        "base_sources",
        "base_artifacts",
        "configuration",
    ):
        if not isinstance(snapshot.get(field), list):
            raise ValueError(f"Makefile preparation {field} is not a list")
    digest_fields = {
        "dependency_digest": snapshot["dependencies"],
        "source_digest": snapshot["base_sources"],
        "artifact_digest": snapshot["base_artifacts"],
        "configuration_digest": snapshot["configuration"],
    }
    for field, value in digest_fields.items():
        if (
            _snapshot_digest(snapshot.get(field), label=field)
            != _stable_digest(value)
            or receipt.get(field) != snapshot.get(field)
        ):
            raise ValueError(f"Makefile preparation {field} is invalid")
    _snapshot_digest(snapshot.get("run_makefile_sha256"), label="run_makefile_sha256")
    if snapshot.get("build_root") != MAKEFILE_BUILD_DIRECTORY.as_posix():
        raise ValueError("Makefile preparation build root is invalid")
    for field in ("make_executable", "coqc_executable", "coqdep_executable"):
        if not isinstance(snapshot.get(field), str) or not snapshot[field]:
            raise ValueError(f"Makefile preparation {field} is invalid")
    if not _same_executable_path(
        snapshot["make_executable"], configured_make_executable(root)
    ):
        raise ValueError("configured GNU Make changed after preparation")
    if not _same_executable_path(
        snapshot["coqc_executable"], configured_coq_executable(root, "coqc")
    ):
        raise ValueError("configured coqc changed after preparation")
    if not _same_executable_path(
        snapshot["coqdep_executable"], configured_coq_executable(root, "coqdep")
    ):
        raise ValueError("configured coqdep changed after preparation")
    if _makefile_configuration_records(root) != snapshot["configuration"]:
        raise ValueError("Makefile configuration changed after preparation")
    metrics = snapshot.get("dependency_metrics")
    if (
        not isinstance(metrics, dict)
        or metrics.get("status") != "resolved"
        or metrics.get("strategy") != "breadth-batched-coqdep"
        or not isinstance(metrics.get("batch_count"), int)
        or not isinstance(metrics.get("coqdep_process_count"), int)
        or not isinstance(metrics.get("node_count"), int)
        or metrics["batch_count"] < 1
        or metrics["coqdep_process_count"] != metrics["batch_count"]
        or metrics["node_count"] < 1
    ):
        raise ValueError("Makefile dependency-resolution metrics are invalid")
    if receipt.get("dependency_metrics") != metrics:
        raise ValueError("Makefile dependency-resolution receipt changed")
    current_cleanup = receipt.get("current_cleanup")
    if (
        not isinstance(current_cleanup, dict)
        or current_cleanup.get("status") != "passed"
        or type(current_cleanup.get("removed_count")) is not int
        or current_cleanup["removed_count"] < 0
    ):
        raise ValueError("Makefile current-family cleanup receipt is invalid")

    target_artifact = _snapshot_relative_path(
        snapshot.get("target"), label="Makefile target", suffix=".vo"
    )
    target_source = target_artifact.with_suffix(".v")
    case_directory = _snapshot_relative_path(
        snapshot.get("case_directory"), label="case_directory"
    )
    case_name = snapshot.get("case_name")
    identity = target_case_identity(target_source)
    if (
        not isinstance(case_name, str)
        or not case_name
        or identity != (case_directory, case_name)
    ):
        raise ValueError("Makefile preparation case identity is invalid")

    def path_list(field: str, *, suffix: str) -> list[Path]:
        values = snapshot[field]
        paths = [
            _snapshot_relative_path(value, label=f"{field} entry", suffix=suffix)
            for value in values
        ]
        if len(set(paths)) != len(paths):
            raise ValueError(f"Makefile preparation {field} contains duplicates")
        return paths

    current_family = path_list("current_family", suffix=".v")
    expected_family = target_case_sources(target_source)
    if current_family != expected_family:
        raise ValueError("Makefile preparation current family is invalid")
    stale_current_outputs = _current_case_source_side_products(root, current_family)
    if stale_current_outputs:
        raise ValueError(
            "Makefile current-family source artifact appeared after preparation: "
            + stale_current_outputs[0].relative_to(root).as_posix()
        )
    current_sources = path_list("current_sources", suffix=".v")

    dependency_graph: dict[Path, tuple[Path, ...]] = {}
    for record in snapshot["dependencies"]:
        if not isinstance(record, dict) or set(record) != {"artifact", "requires"}:
            raise ValueError("Makefile dependency record is invalid")
        artifact = _snapshot_relative_path(
            record["artifact"], label="dependency artifact", suffix=".vo"
        )
        requires_value = record["requires"]
        if not isinstance(requires_value, list):
            raise ValueError("Makefile dependency requires is not a list")
        requires = tuple(
            _snapshot_relative_path(
                value, label="required dependency artifact", suffix=".vo"
            ).with_suffix(".v")
            for value in requires_value
        )
        if len(set(requires)) != len(requires):
            raise ValueError("Makefile dependency record contains duplicates")
        source = artifact.with_suffix(".v")
        if source in dependency_graph:
            raise ValueError("Makefile dependency graph contains duplicate nodes")
        dependency_graph[source] = requires
    graph_sources = set(dependency_graph)
    if target_source not in graph_sources:
        raise ValueError("Makefile dependency graph omits its target")
    if any(
        dependency not in graph_sources
        for dependencies in dependency_graph.values()
        for dependency in dependencies
    ):
        raise ValueError("Makefile dependency graph contains an outside edge")
    if set(_dependency_closure(dependency_graph, target_source)) != graph_sources:
        raise ValueError("Makefile dependency graph contains unreachable nodes")
    expected_dependency_records = [
        {
            "artifact": source.with_suffix(".vo").as_posix(),
            "requires": [
                dependency.with_suffix(".vo").as_posix()
                for dependency in sorted(
                    dependency_graph[source], key=lambda item: item.as_posix()
                )
            ],
        }
        for source in sorted(graph_sources, key=lambda item: item.as_posix())
    ]
    if snapshot["dependencies"] != expected_dependency_records:
        raise ValueError("Makefile dependency records are not canonical")

    def hashed_records(field: str, *, suffix: str) -> dict[Path, str]:
        records: dict[Path, str] = {}
        for record in snapshot[field]:
            if (
                not isinstance(record, dict)
                or set(record) != {"relative_path", "sha256"}
            ):
                raise ValueError(f"Makefile preparation {field} record is invalid")
            relative = _snapshot_relative_path(
                record["relative_path"], label=f"{field} path", suffix=suffix
            )
            if relative in records:
                raise ValueError(f"Makefile preparation {field} contains duplicates")
            records[relative] = _snapshot_digest(
                record["sha256"], label=f"{field} sha256"
            )
        if list(records) != sorted(records, key=lambda item: item.as_posix()):
            raise ValueError(f"Makefile preparation {field} is not canonical")
        return records

    base_sources = hashed_records("base_sources", suffix=".v")
    base_artifacts = hashed_records("base_artifacts", suffix=".vo")
    if {source.with_suffix(".vo") for source in base_sources} != set(base_artifacts):
        raise ValueError("Makefile base source/artifact sets disagree")
    family_set = set(current_family)
    if set(current_sources) != graph_sources & family_set:
        raise ValueError("Makefile current-source closure is invalid")
    if set(base_sources) != graph_sources - family_set:
        raise ValueError("Makefile trusted-base closure is invalid")
    expected_current_dependencies = [
        {
            "source": source.as_posix(),
            "requires": [
                dependency.as_posix()
                for dependency in sorted(
                    dependency_graph[source], key=lambda item: item.as_posix()
                )
                if dependency in set(current_sources)
            ],
        }
        for source in sorted(current_sources, key=lambda item: item.as_posix())
    ]
    if snapshot["current_dependencies"] != expected_current_dependencies:
        raise ValueError("Makefile current dependency records are invalid")
    if (
        metrics.get("node_count") != len(dependency_graph)
        or metrics.get("source_count") != len(dependency_graph)
        or receipt.get("base_artifact_count") != len(base_artifacts)
        or receipt.get("current_source_count") != len(current_sources)
        or receipt.get("returncode") != 0
        or type(receipt.get("rebuilt_count")) is not int
        or not 0 <= receipt["rebuilt_count"] <= len(base_artifacts)
    ):
        raise ValueError("Makefile preparation counts are invalid")
    run_makefile_text = snapshot.get("run_makefile")
    if run_makefile_text is not None:
        run_makefile_rel = _snapshot_relative_path(
            run_makefile_text, label="run-local exact Makefile"
        )
        run_makefile = fixed_path_under(
            root / run_makefile_rel, root, label="run-local exact Makefile"
        )
        if (
            run_root_from_path(run_makefile, root) is None
            or run_makefile.name != RUN_MAKEFILE_NAME
        ):
            raise ValueError("run-local exact Makefile path is invalid")
        _regular_file(run_makefile, label="run-local exact Makefile")
        if file_sha256(run_makefile) != snapshot.get("run_makefile_sha256"):
            raise ValueError("run-local exact Makefile changed after preparation")
    for relative, digest in base_sources.items():
        path = _fixed_repository_file(
            root, relative, label="Makefile dependency source"
        )
        if file_sha256(path) != digest:
            raise ValueError(f"Makefile dependency source changed: {relative}")
    for relative, digest in base_artifacts.items():
        path = _fixed_repository_file(
            root, relative, label="Makefile-prepared base artifact"
        )
        if file_sha256(path) != digest:
            raise ValueError(f"Makefile-prepared base artifact changed: {relative}")
    return snapshot


def _require_validated_dune_snapshot(
    *,
    workspace_root: Path,
    receipt: Mapping[str, Any] | None,
    expected_source_goal_version: str | None = None,
    repair: str = "Rerun the controller-owned build-preparation action.",
) -> dict[str, Any]:
    try:
        return _validated_dune_snapshot(
            workspace_root=workspace_root,
            receipt=receipt,
            expected_source_goal_version=expected_source_goal_version,
        )
    except (
        CoqBuildPlanError,
        OSError,
        UnicodeError,
        ValueError,
        json.JSONDecodeError,
    ) as exc:
        raise CoqBuildPlanError(
            category="freshness",
            kind="makefile-preparation-stale",
            message=str(exc) or repr(exc),
            repair=repair,
        ) from exc


def dune_preparation_receipt_errors(
    *,
    workspace_root: Path,
    receipt: Mapping[str, Any] | None,
    expected_source_goal_version: str | None = None,
) -> list[str]:
    try:
        _validated_dune_snapshot(
            workspace_root=workspace_root,
            receipt=receipt,
            expected_source_goal_version=expected_source_goal_version,
        )
    except (CoqBuildPlanError, OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return [str(exc) or repr(exc)]
    return []


def _receipt_from_run(
    *, workspace_root: Path, build_workspace: Path
) -> Mapping[str, Any] | None:
    root = workspace_root.expanduser().resolve()
    run_root = run_root_from_path(build_workspace, root)
    if run_root is None:
        return None
    state_path = root / "reports" / run_root.name / "controller_state.json"
    try:
        state = json.loads(_regular_file(state_path, label="controller state").read_text(encoding="utf-8"))
    except (CoqBuildPlanError, OSError, UnicodeError, ValueError, json.JSONDecodeError):
        return None
    receipt = state.get("dune_preparation") if isinstance(state, dict) else None
    return receipt if isinstance(receipt, Mapping) else None


def dune_snapshot_for_preserved_build(
    *,
    workspace_root: Path,
    receipt: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Validate the caller's preparation and return the base closure it selects."""

    snapshot = _require_validated_dune_snapshot(
        workspace_root=workspace_root,
        receipt=receipt,
    )
    return {
        "digest": snapshot["artifact_digest"],
        "file_count": len(snapshot["base_artifacts"]),
        "_snapshot": snapshot,
    }


def _normalized_overlay_map(
    overlays: Mapping[Path, Path] | None,
) -> dict[Path, Path]:
    result: dict[Path, Path] = {}
    for raw_destination, raw_source in (overlays or {}).items():
        destination = Path(raw_destination.as_posix())
        source = raw_source.expanduser().resolve()
        if destination.is_absolute() or ".." in destination.parts or destination.suffix != ".v":
            raise CoqBuildPlanError(
                category="contract",
                kind="source-stage-boundary",
                message=f"invalid current overlay destination: {destination}",
                repair="Use only controller-derived current-case .v overlay destinations.",
            )
        _regular_file(source, label="current overlay source")
        result[destination] = source
    return result


def _copy_if_changed(source: Path, destination: Path) -> bool:
    _regular_file(source, label="current source")
    if destination.is_file() and not path_is_link_like(destination):
        if destination.stat().st_size == source.stat().st_size and file_sha256(destination) == file_sha256(source):
            return False
    destination.parent.mkdir(parents=True, exist_ok=True)
    atomic_copy_file(source, destination, suffix=".stage", preserve_metadata=True)
    return True


def _path_spellings(path: Path) -> set[str]:
    text = str(path)
    values = {text, text.replace("/", "\\"), text.replace("\\", "/")}
    if text.endswith(".v"):
        stem = text[:-2]
        values.update({stem, stem.replace("/", "\\"), stem.replace("\\", "/")})
    return values


def normalize_generated_case_imports(
    *,
    workspace_root: Path,
    build_workspace: Path,
    current_case_sources: Iterable[Path],
) -> list[str]:
    root = workspace_root.expanduser().resolve()
    build = build_workspace.expanduser().resolve()
    sources = [Path(item.as_posix()) for item in current_case_sources]
    replacements: dict[str, str] = {}
    for relative in sources:
        for spelling in _path_spellings(root / relative) | _path_spellings(build / relative):
            replacements[spelling] = relative.stem
        replacements[relative.with_suffix("").as_posix()] = relative.stem
    changed: list[str] = []
    for relative in sources:
        path = build / relative
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        updated = text
        for old, new in sorted(replacements.items(), key=lambda item: len(item[0]), reverse=True):
            updated = updated.replace(old, new)
        if updated != text:
            atomic_write_text(path, updated, suffix=".normalize")
            changed.append(relative.as_posix())
    return changed


def normalize_local_case_module_references(
    *,
    workspace_root: Path,
    build_workspace: Path,
    current_case_sources: Iterable[Path],
) -> list[str]:
    root = workspace_root.expanduser().resolve()
    build = build_workspace.expanduser().resolve()
    sources = [Path(item.as_posix()) for item in current_case_sources]
    local: dict[Path, dict[str, str]] = {}
    source_texts: dict[Path, str] = {}
    for relative in sources:
        logical = relative_to_logical_module(relative)
        if logical:
            local.setdefault(relative.parent, {})[relative.stem] = logical
        path = build / relative
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        source_texts[relative] = text
        for module in _required_modules(text):
            sibling = relative.parent / f"{module}.v"
            sibling_logical = relative_to_logical_module(sibling)
            if "." not in module and sibling_logical and (root / sibling).is_file():
                local.setdefault(relative.parent, {})[module] = sibling_logical
    changed: list[str] = []
    for relative in sources:
        path = build / relative
        mapping = local.get(relative.parent, {})
        text = source_texts.get(relative)
        if text is None or not mapping:
            continue
        lines: list[str] = []
        touched = False
        for line in text.splitlines(keepends=True):
            newline = "\n" if line.endswith("\n") else ""
            body = line[:-1] if newline else line
            match = re.match(
                r"^(\s*)Require\s+(Import|Export)\s+([A-Za-z0-9_'\s]+)\.(\s*)$",
                body,
            )
            if match:
                indent, mode, modules_text, trailing = match.groups()
                modules = modules_text.split()
                logicals = [mapping.get(module) for module in modules]
                prefixes = {item.rsplit(".", 1)[0] for item in logicals if item}
                if modules and all(logicals) and len(prefixes) == 1:
                    lines.append(
                        f"{indent}From {prefixes.pop()} Require {mode} "
                        f"{' '.join(modules)}.{trailing}{newline}"
                    )
                    touched = True
                    continue
            lines.append(line)
        if touched:
            atomic_write_text(path, "".join(lines), suffix=".qualify")
            changed.append(relative.as_posix())
    return changed


def remove_auto_manual_proof_overlaps(
    *, build_workspace: Path, current_case_sources: Iterable[Path]
) -> list[str]:
    build = build_workspace.expanduser().resolve()
    sources = {Path(item.as_posix()) for item in current_case_sources}
    changed: list[str] = []
    for auto_rel in sorted(sources, key=lambda item: item.as_posix()):
        if not auto_rel.name.endswith("_proof_auto.v"):
            continue
        manual_rel = auto_rel.with_name(auto_rel.name.replace("_proof_auto.v", "_proof_manual.v"))
        auto_path = build / auto_rel
        manual_path = build / manual_rel
        if manual_rel not in sources or not auto_path.is_file() or not manual_path.is_file():
            continue
        manual_names = {
            match.group(2)
            for match in PROOF_DECLARATION_RE.finditer(manual_path.read_text(encoding="utf-8"))
        }
        auto_text = auto_path.read_text(encoding="utf-8")
        updated = PROOF_BLOCK_RE.sub(
            lambda match: "" if match.group(1) in manual_names else match.group(0),
            auto_text,
        )
        if updated != auto_text:
            atomic_write_text(auto_path, updated, suffix=".dedupe")
            changed.append(auto_rel.as_posix())
    return changed


def remove_target_case_side_products(
    build_workspace: Path, sources: Iterable[Path]
) -> list[str]:
    build = build_workspace.expanduser().resolve()
    removed: list[str] = []
    for relative in sources:
        source = build / relative
        candidates = [source.with_suffix(suffix) for suffix in COQ_SIDE_PRODUCT_SUFFIXES]
        candidates.append(source.parent / f".{source.stem}.aux")
        for candidate in candidates:
            if candidate.exists() or candidate.is_symlink():
                if path_is_link_like(candidate) or not candidate.is_file():
                    raise CoqBuildPlanError(
                        category="contract",
                        kind="build-side-product-boundary",
                        message=f"build side product is not a regular file: {candidate}",
                        repair="Restore the controller-owned build directory.",
                    )
                candidate.unlink()
                removed.append(candidate.relative_to(build).as_posix())
    return sorted(set(removed))


def _module_relative_for_source(
    *, module: str, source: Path, snapshot: Mapping[str, Any]
) -> Path | None:
    mapped = logical_module_to_relative(module)
    if mapped is not None:
        return mapped
    if _is_standard_module(module):
        return None
    if "." not in module:
        sibling = source.parent / f"{module}.v"
        known = {
            Path(item) for item in snapshot["current_sources"]
        } | {
            Path(record["relative_path"]) for record in snapshot["base_sources"]
        }
        if sibling in known:
            return sibling
        candidates = sorted(
            (item for item in known if item.stem == module),
            key=lambda item: item.as_posix(),
        )
        if len(candidates) == 1:
            return candidates[0]
        if len(candidates) > 1:
            raise CoqBuildPlanError(
                category="contract",
                kind="ambiguous-proof-time-import",
                message=(
                    f"ambiguous unqualified import {module} in {source.as_posix()}: "
                    + ", ".join(item.as_posix() for item in candidates)
                ),
                repair="Use a fully qualified import in the annotation-owned source.",
            )
    return None


def _validate_fixed_dependencies(
    *,
    snapshot: Mapping[str, Any],
    source_texts: Mapping[Path, str],
) -> None:
    current = {Path(item) for item in snapshot["current_sources"]}
    base = {
        Path(record["relative_path"]).with_suffix(".v")
        for record in snapshot["base_artifacts"]
    }
    allowed = current | base
    fixed_edges = {
        Path(record["source"]): {Path(item) for item in record["requires"]}
        for record in snapshot["current_dependencies"]
    }
    for source, text in source_texts.items():
        for module in _dependency_modules(text, source_label=source):
            dependency = _module_relative_for_source(
                module=module, source=source, snapshot=snapshot
            )
            if dependency is None:
                if _is_external_module(module):
                    continue
                raise CoqBuildPlanError(
                    category="tooling",
                    kind="makefile-dependency-not-prepared",
                    message=(
                        f"proof-time import {module} in {source.as_posix()} is not "
                        "present in the accepted Makefile dependency snapshot"
                    ),
                    repair=(
                        "Return to annotation, add the required import there, and "
                        "accept a new Makefile snapshot before proving."
                    ),
                )
            if dependency not in allowed:
                raise CoqBuildPlanError(
                    category="tooling",
                    kind="makefile-dependency-not-prepared",
                    message=(
                        f"proof-time dependency is outside the accepted Makefile snapshot: "
                        f"{dependency.as_posix()}"
                    ),
                    repair="Return to annotation and rebuild the fixed Makefile dependency snapshot.",
                )
            if source in fixed_edges and dependency in current and dependency not in fixed_edges[source]:
                raise CoqBuildPlanError(
                    category="contract",
                    kind="current-dependency-changed-after-annotation",
                    message=(
                        f"current dependency edge changed after annotation: "
                        f"{source.as_posix()} -> {dependency.as_posix()}"
                    ),
                    repair="Return to annotation so Makefile preparation can accept the new dependency graph.",
                )


def _current_dependency_map(snapshot: Mapping[str, Any]) -> dict[Path, tuple[Path, ...]]:
    return {
        Path(record["source"]): tuple(Path(item) for item in record["requires"])
        for record in snapshot["current_dependencies"]
    }


def _topological_current_order(
    snapshot: Mapping[str, Any], roots: Iterable[Path] | None = None
) -> list[Path]:
    graph = _current_dependency_map(snapshot)
    selected = set(graph) if roots is None else set(roots)
    order: list[Path] = []
    visiting: set[Path] = set()
    visited: set[Path] = set()

    def visit(source: Path) -> None:
        if source in visited or source not in graph:
            return
        if source in visiting:
            raise CoqBuildPlanError(
                category="contract",
                kind="current-dependency-cycle",
                message=f"current dependency cycle at {source.as_posix()}",
                repair="Return to annotation and repair the current module cycle.",
            )
        visiting.add(source)
        for dependency in graph[source]:
            visit(dependency)
        visiting.remove(source)
        visited.add(source)
        order.append(source)

    for root in sorted(selected, key=lambda item: item.as_posix()):
        visit(root)
    return order


def _current_entry(build_workspace: Path, case_directory: Path) -> CoqLoadPathEntry:
    marker = case_directory / "__qcp_marker__.v"
    logical = relative_to_logical_module(marker)
    if logical is None:
        raise CoqBuildPlanError(
            category="contract",
            kind="load-path-plan-mismatch",
            message=f"unsupported current case directory: {case_directory}",
            repair="Keep the formal directory under a configured Rocq load root.",
        )
    return CoqLoadPathEntry(
        "-R", (build_workspace / case_directory).resolve(), logical.rsplit(".", 1)[0]
    )


def make_coqc_argv(
    target_file: Path,
    *,
    workspace_root: Path,
    build_workspace: Path,
    case_directory: Path,
) -> list[str]:
    entries = (*_base_load_path_entries(workspace_root), _current_entry(build_workspace, case_directory))
    return [
        configured_coq_executable(workspace_root, "coqc"),
        "-q",
        *_render_load_path_flags(entries),
        target_file.as_posix(),
    ]


def make_coqtop_argv(
    debug_script: Path,
    *,
    workspace_root: Path,
    build_workspace: Path,
    case_directory: Path,
) -> list[str]:
    entries = (*_base_load_path_entries(workspace_root), _current_entry(build_workspace, case_directory))
    return [
        configured_coq_executable(workspace_root, "coqtop"),
        "-q",
        "-batch",
        *_render_load_path_flags(entries),
        "-l",
        os.fspath(debug_script),
    ]


def _run_rocq(
    argv: Sequence[str], *, cwd: Path, timeout_seconds: float
) -> dict[str, Any]:
    result = run_bounded_process(
        argv,
        cwd=cwd,
        timeout_seconds=timeout_seconds,
        timeout_message=f"\nRocq command timed out after {timeout_seconds:g} seconds.",
        detached_pipe_message="\nRocq cleanup could not fully drain a detached pipe.",
        launch_error_prefix="cannot launch Rocq: ",
    )
    combined = "\n".join(item for item in (result.stdout, result.stderr) if item)
    return {
        "returncode": result.returncode,
        "stdout_tail": tail(result.stdout),
        "stderr_tail": tail(result.stderr),
        "first_diagnostic": extract_first_coq_failure(combined),
    }


def _rocq_deadline_failure(target: Path, timeout_seconds: float) -> dict[str, Any]:
    return {
        "returncode": 124,
        "stdout_tail": "",
        "stderr_tail": (
            f"Rocq command budget of {timeout_seconds:g} seconds was exhausted "
            f"before starting {target.as_posix()}."
        ),
        "first_diagnostic": None,
        "failed_target_file": target.as_posix(),
    }


def _cache_root(workspace_root: Path, build_workspace: Path) -> Path | None:
    run_root = run_root_from_path(build_workspace, workspace_root)
    return None if run_root is None else run_root / "_coq_builds" / "current"


def _compile_current_sources(
    *,
    workspace_root: Path,
    build_workspace: Path,
    snapshot: Mapping[str, Any],
    order: Sequence[Path],
    source_digests: Mapping[Path, str],
    deadline: float,
    timeout_seconds: float,
) -> tuple[list[str], int, float, dict[str, Any] | None]:
    started = time.monotonic()
    cache_root = _cache_root(workspace_root, build_workspace)
    if cache_root is not None:
        cache_root.mkdir(parents=True, exist_ok=True)
    reused = 0
    compiled: list[str] = []
    dependency_digests: dict[Path, str] = {}
    case_directory = Path(str(snapshot["case_directory"]))
    current_dependencies = _current_dependency_map(snapshot)
    for source in order:
        source_path = build_workspace / source
        dependencies = current_dependencies.get(source, ())
        source_digest = source_digests.get(source)
        if not source_digest:
            raise CoqBuildPlanError(
                category="contract",
                kind="current-source-digest-missing",
                message=f"staged current source digest is missing: {source.as_posix()}",
                repair="Restage the fixed current-case sources and rerun the check.",
            )
        key_payload = {
            "source": source.as_posix(),
            "source_sha256": source_digest,
            "dependencies": [
                {
                    "source": item.as_posix(),
                    "vo_sha256": dependency_digests.get(item),
                }
                for item in dependencies
            ],
            "base_artifact_digest": snapshot["artifact_digest"],
            "configuration_digest": snapshot["configuration_digest"],
            "coqc": configured_coq_executable(workspace_root, "coqc"),
        }
        key = _stable_digest(key_payload)
        cached = cache_root / f"{key}.vo" if cache_root is not None else None
        destination = source_path.with_suffix(".vo")
        if cached is not None and cached.is_file() and not path_is_link_like(cached):
            atomic_copy_file(cached, destination, suffix=".cache-restore", preserve_metadata=False)
            reused += 1
            dependency_digests[source] = file_sha256(destination)
            continue
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return (
                compiled,
                reused,
                time.monotonic() - started,
                _rocq_deadline_failure(source, timeout_seconds),
            )
        remove_target_case_side_products(build_workspace, [source])
        argv = make_coqc_argv(
            source,
            workspace_root=workspace_root,
            build_workspace=build_workspace,
            case_directory=case_directory,
        )
        result = _run_rocq(argv, cwd=build_workspace, timeout_seconds=remaining)
        if result["returncode"] != 0:
            return compiled, reused, time.monotonic() - started, {
                **result,
                "failed_target_file": source.as_posix(),
                "argv": argv,
            }
        _regular_file(destination, label="locally compiled current artifact")
        dependency_digests[source] = file_sha256(destination)
        if cached is not None:
            atomic_copy_file(destination, cached, suffix=".cache-publish", preserve_metadata=False)
        compiled.append(source.as_posix())
    return compiled, reused, time.monotonic() - started, None


def _write_group_check_wrapper(
    build_workspace: Path, target_rel: Path, group_check: Mapping[str, Any]
) -> None:
    case_theory = str(group_check.get("case_theory") or "").strip()
    require_modules = [str(item).strip() for item in group_check.get("require_modules", []) if str(item).strip()]
    assigned = [str(item).strip() for item in group_check.get("assigned_witnesses", []) if str(item).strip()]
    if not case_theory or not require_modules or not assigned:
        raise CoqBuildPlanError(
            category="contract",
            kind="group-check-wrapper",
            message="group-check wrapper inputs are incomplete",
            repair="Restore the controller-derived group assignment.",
        )
    path = build_workspace / target_rel
    path.parent.mkdir(parents=True, exist_ok=True)
    text = (
        "(* Generated build-workspace-only group check wrapper. *)\n"
        f"From {case_theory} Require Import {' '.join(require_modules)}.\n\n"
        + "\n".join(f"Check {name}." for name in assigned)
        + "\n"
    )
    atomic_write_text(path, text, suffix=".group-check")


def _coq_failure_result(
    *,
    target_file: Path,
    target_kind: str,
    source_goal_version: str | None,
    build_workspace: Path,
    started: float,
    error: CoqBuildPlanError,
) -> dict[str, Any]:
    return {
        "status": "failed",
        "returncode": 2,
        "target_file": target_file.as_posix(),
        "target_kind": target_kind,
        "source_goal_version": source_goal_version,
        "build_workspace": str(build_workspace),
        "dependency_mode": "makefile-snapshot",
        "first_failure": error.first_failure(),
        "stderr_tail": str(error),
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def run_coqc_check(
    *,
    workspace_root: Path,
    build_workspace: Path,
    target_file: Path,
    target_kind: str,
    source_goal_version: str | None,
    timeout_seconds: int | float | None = COQ_COMMAND_TIMEOUT_SECONDS,
    group_check: dict[str, Any] | None = None,
    overlays: dict[Path, Path] | None = None,
    incremental: bool = False,
    current_case_anchor: Path | None = None,
    dune_preparation: Mapping[str, Any] | None = None,
    _reuse_dune_snapshot: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Compile/check current files using one sealed Makefile dependency graph."""

    started = time.monotonic()
    timeout = float(
        COQ_COMMAND_TIMEOUT_SECONDS if timeout_seconds is None else timeout_seconds
    )
    deadline = started + timeout
    root = workspace_root.expanduser().resolve()
    build = Path(os.path.abspath(os.fspath(build_workspace.expanduser())))
    target_rel = Path(target_file.as_posix())
    layout_error = build_workspace_layout_error(root, build)
    if layout_error:
        return _coq_failure_result(
            target_file=target_rel,
            target_kind=target_kind,
            source_goal_version=source_goal_version,
            build_workspace=build,
            started=started,
            error=CoqBuildPlanError(
                category="contract",
                kind="build-workspace-layout",
                message=layout_error,
                repair="Use the controller-derived run-local build directory.",
            ),
        )
    try:
        if _reuse_dune_snapshot is None:
            receipt = dune_preparation or _receipt_from_run(
                workspace_root=root, build_workspace=build
            )
            snapshot = _require_validated_dune_snapshot(
                workspace_root=root,
                receipt=receipt,
                expected_source_goal_version=(source_goal_version or None),
                repair=(
                    "Rerun the controller-owned build-preparation action before proving."
                ),
            )
        else:
            snapshot = _strict_snapshot(_reuse_dune_snapshot)
            if (
                source_goal_version is not None
                and snapshot.get("source_goal_version") != source_goal_version
            ):
                raise CoqBuildPlanError(
                    category="freshness",
                    kind="makefile-preparation-stale",
                    message="Makefile preparation source_goal_version is stale",
                    repair=(
                        "Rerun the controller-owned build-preparation action before proving."
                    ),
                )
        anchor = current_case_anchor or target_rel
        identity = target_case_identity(
            target_rel,
            case_anchor=anchor,
            group_check=group_check,
            overlays=overlays,
        )
        if identity != (Path(str(snapshot["case_directory"])), str(snapshot["case_name"])):
            raise CoqBuildPlanError(
                category="contract",
                kind="load-path-plan-mismatch",
                message="check target identity differs from the accepted Makefile snapshot",
                repair="Use the persisted target_files and current run snapshot.",
            )
        build.mkdir(parents=True, exist_ok=True)
        overlay_map = _normalized_overlay_map(overlays)
        current_sources = [Path(item) for item in snapshot["current_sources"]]
        staged: list[str] = []
        overlaid: list[str] = []
        for relative in current_sources:
            source = overlay_map.get(relative, root / relative)
            if _copy_if_changed(source, build / relative):
                staged.append(relative.as_posix())
            if relative in overlay_map:
                overlaid.append(relative.as_posix())
        normalize_generated_case_imports(
            workspace_root=root,
            build_workspace=build,
            current_case_sources=current_sources,
        )
        normalize_local_case_module_references(
            workspace_root=root,
            build_workspace=build,
            current_case_sources=current_sources,
        )
        remove_auto_manual_proof_overlaps(
            build_workspace=build, current_case_sources=current_sources
        )
        # Validate the exact staged bytes that coqc will consume. In
        # particular, local unqualified imports are normalized to their full
        # project module before the fixed-snapshot boundary is checked.
        source_texts = {
            relative: (build / relative).read_text(encoding="utf-8")
            for relative in current_sources
        }
        _validate_fixed_dependencies(snapshot=snapshot, source_texts=source_texts)
        order = _topological_current_order(snapshot)
        compiled, reused, compile_seconds, compile_failure = _compile_current_sources(
            workspace_root=root,
            build_workspace=build,
            snapshot=snapshot,
            order=order,
            source_digests={
                relative: sha256_text(text)
                for relative, text in source_texts.items()
            },
            deadline=deadline,
            timeout_seconds=timeout,
        )
        if compile_failure is not None:
            return {
                "status": "failed",
                "target_file": target_rel.as_posix(),
                "target_kind": target_kind,
                "source_goal_version": source_goal_version,
                "configured_coqc": configured_coq_executable(root, "coqc"),
                "build_workspace": str(build),
                "dependency_mode": "makefile-snapshot",
                "reused_base_vo_count": len(snapshot["base_artifacts"]),
                "reused_current_vo_count": reused,
                "staged_current_source_count": len(current_sources),
                "overlaid_sources": sorted(overlaid),
                "recompiled_target_files": compiled,
                "current_compile_seconds": round(compile_seconds, 6),
                "returncode": compile_failure["returncode"],
                "first_failure": compile_failure.get("first_diagnostic") or {
                    "category": "verification",
                    "kind": "coqc-failed",
                    "message": compile_failure.get("stderr_tail") or compile_failure.get("stdout_tail") or "coqc failed",
                    "repair": "Repair the current proof/spec and rerun the unchanged check.",
                },
                "failed_target_file": compile_failure.get("failed_target_file"),
                "stdout_tail": compile_failure.get("stdout_tail", ""),
                "stderr_tail": compile_failure.get("stderr_tail", ""),
                "elapsed_seconds": round(time.monotonic() - started, 6),
            }
        actual_target = target_rel
        if target_kind == "group-check":
            _write_group_check_wrapper(build, target_rel, group_check or {})
        if actual_target not in current_sources:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                target_result = _rocq_deadline_failure(actual_target, timeout)
            else:
                target_result = None
            argv = make_coqc_argv(
                actual_target,
                workspace_root=root,
                build_workspace=build,
                case_directory=Path(str(snapshot["case_directory"])),
            )
            if target_result is None:
                target_result = _run_rocq(
                    argv, cwd=build, timeout_seconds=remaining
                )
            if target_result["returncode"] != 0:
                return {
                    "status": "failed",
                    "target_file": target_rel.as_posix(),
                    "target_kind": target_kind,
                    "source_goal_version": source_goal_version,
                    "configured_coqc": argv[0],
                    "build_workspace": str(build),
                    "dependency_mode": "makefile-snapshot",
                    "reused_base_vo_count": len(snapshot["base_artifacts"]),
                    "reused_current_vo_count": reused,
                    "staged_current_source_count": len(current_sources),
                    "overlaid_sources": sorted(overlaid),
                    "recompiled_target_files": compiled,
                    "current_compile_seconds": round(compile_seconds, 6),
                    "returncode": target_result["returncode"],
                    "first_failure": target_result.get("first_diagnostic") or {
                        "category": "verification",
                        "kind": "coqc-failed",
                        "message": target_result.get("stderr_tail") or target_result.get("stdout_tail") or "coqc failed",
                        "repair": "Repair the current proof and rerun the unchanged check.",
                    },
                    "stdout_tail": target_result.get("stdout_tail", ""),
                    "stderr_tail": target_result.get("stderr_tail", ""),
                    "elapsed_seconds": round(time.monotonic() - started, 6),
                }
            compiled.append(actual_target.as_posix())
        return {
            "status": "passed",
            "returncode": 0,
            "target_file": target_rel.as_posix(),
            "target_kind": target_kind,
            "source_goal_version": source_goal_version,
            "configured_coqc": configured_coq_executable(root, "coqc"),
            "build_workspace": str(build),
            "dependency_mode": "makefile-snapshot",
            "reused_base_vo_count": len(snapshot["base_artifacts"]),
            "reused_current_vo_count": reused,
            "staged_current_source_count": len(current_sources),
            "current_case_family_count": len(snapshot["current_family"]),
            "overlaid_sources": sorted(overlaid),
            "incremental_development_check": bool(incremental),
            "recompiled_target_files": compiled,
            "current_compile_seconds": round(compile_seconds, 6),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
    except CoqBuildPlanError as exc:
        return _coq_failure_result(
            target_file=target_rel,
            target_kind=target_kind,
            source_goal_version=source_goal_version,
            build_workspace=build,
            started=started,
            error=exc,
        )
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return _coq_failure_result(
            target_file=target_rel,
            target_kind=target_kind,
            source_goal_version=source_goal_version,
            build_workspace=build,
            started=started,
            error=CoqBuildPlanError(
                category="tooling",
                kind="coq-check-preparation-failed",
                message=str(exc) or repr(exc),
                repair="Restore the accepted Makefile snapshot and fixed current files.",
            ),
        )


def run_coqtop_debug(
    *,
    workspace_root: Path,
    build_workspace: Path,
    debug_script: Path,
    source_goal_version: str | None,
    timeout_seconds: int | float | None = COQ_COMMAND_TIMEOUT_SECONDS,
    overlays: dict[Path, Path] | None = None,
    reuse_existing_build: bool = False,
    current_case_anchor: Path | None = None,
    _reuse_dune_snapshot: dict[str, Any] | None = None,
) -> dict[str, Any]:
    started = time.monotonic()
    timeout = float(
        COQ_COMMAND_TIMEOUT_SECONDS if timeout_seconds is None else timeout_seconds
    )
    deadline = started + timeout
    root = workspace_root.expanduser().resolve()
    build = Path(os.path.abspath(os.fspath(build_workspace.expanduser())))
    debug_rel = Path(debug_script.as_posix())
    try:
        layout_error = build_workspace_layout_error(root, build)
        if layout_error:
            raise CoqBuildPlanError(
                category="contract",
                kind="build-workspace-layout",
                message=layout_error,
                repair="Use the controller-derived run-local build directory.",
            )
        if debug_rel.is_absolute() or ".." in debug_rel.parts:
            raise CoqBuildPlanError(
                category="contract",
                kind="debug-script-path-resolution",
                message=(
                    "Rocq debug script must be a normalized build-relative path: "
                    + debug_rel.as_posix()
                ),
                repair="Use the one controller-authorized debug script path.",
            )
        receipt = None
        if _reuse_dune_snapshot is None:
            receipt = _receipt_from_run(
                workspace_root=root, build_workspace=build
            )
            snapshot = _require_validated_dune_snapshot(
                workspace_root=root,
                receipt=receipt,
                expected_source_goal_version=(source_goal_version or None),
            )
        else:
            snapshot = _strict_snapshot(_reuse_dune_snapshot)
            if (
                source_goal_version is not None
                and snapshot.get("source_goal_version") != source_goal_version
            ):
                raise CoqBuildPlanError(
                    category="freshness",
                    kind="makefile-preparation-stale",
                    message="Makefile preparation source_goal_version is stale",
                    repair="Rerun the controller-owned build-preparation action.",
                )
        if not reuse_existing_build:
            preparation = run_coqc_check(
                workspace_root=root,
                build_workspace=build,
                target_file=(current_case_anchor or Path(snapshot["current_sources"][-1])),
                target_kind="debug-preparation",
                source_goal_version=source_goal_version,
                timeout_seconds=max(0.0, deadline - time.monotonic()),
                overlays=overlays,
                current_case_anchor=current_case_anchor,
                dune_preparation=receipt,
                _reuse_dune_snapshot=snapshot,
            )
            if preparation.get("status") != "passed":
                return {
                    **preparation,
                    "tool": "coqtop",
                    "kind": "coqtop_debug",
                    "debug_script": debug_rel.as_posix(),
                }
        else:
            for relative_text in snapshot["current_sources"]:
                relative = Path(relative_text)
                _regular_file(
                    build / relative.with_suffix(".vo"),
                    label="preserved debug current artifact",
                )
        try:
            debug_path = fixed_path_under(
                build / debug_rel,
                build,
                label="Rocq debug script",
            )
        except SystemExit as exc:
            raise CoqBuildPlanError(
                category="contract",
                kind="debug-script-path-resolution",
                message=str(exc),
                repair="Restore the one fixed debug script without path indirection.",
            ) from exc
        debug_path = _regular_file(debug_path, label="Rocq debug script")
        debug_payload = debug_path.read_bytes()
        debug_digest = sha256_bytes(debug_payload)
        debug_metadata = debug_path.stat()
        debug_identity = (
            debug_metadata.st_dev,
            debug_metadata.st_ino,
            debug_metadata.st_mode,
            debug_metadata.st_size,
            debug_metadata.st_mtime_ns,
        )
        debug_text = debug_payload.decode("utf-8")
        _validate_fixed_dependencies(
            snapshot=snapshot, source_texts={debug_rel: debug_text}
        )
        argv = make_coqtop_argv(
            debug_path,
            workspace_root=root,
            build_workspace=build,
            case_directory=Path(str(snapshot["case_directory"])),
        )
        load_argument = argv[-1]
        resolved_script = Path(
            os.path.abspath(os.fspath(Path(load_argument).expanduser()))
        )
        if resolved_script != debug_path:
            raise CoqBuildPlanError(
                category="contract",
                kind="debug-script-path-resolution",
                message=(
                    "coqtop load argument does not resolve to the authorized "
                    f"debug script: {resolved_script} != {debug_path}"
                ),
                repair=(
                    "Use the validated absolute debug script as the coqtop "
                    "load argument."
                ),
                evidence={
                    "child_cwd": str(build),
                    "load_argument": load_argument,
                    "authorized_script_path": str(debug_path),
                },
            )
        remaining = deadline - time.monotonic()
        result = (
            _rocq_deadline_failure(debug_rel, timeout)
            if remaining <= 0
            else _run_rocq(argv, cwd=build, timeout_seconds=remaining)
        )
        post_failure: CoqBuildPlanError | None = None
        try:
            post_path = fixed_path_under(
                build / debug_rel,
                build,
                label="Rocq debug script after coqtop",
            )
            post_digest = file_sha256(
                _regular_file(post_path, label="Rocq debug script after coqtop")
            )
            post_metadata = post_path.stat()
            post_identity = (
                post_metadata.st_dev,
                post_metadata.st_ino,
                post_metadata.st_mode,
                post_metadata.st_size,
                post_metadata.st_mtime_ns,
            )
            if (
                post_path != debug_path
                or post_digest != debug_digest
                or post_identity != debug_identity
            ):
                post_failure = CoqBuildPlanError(
                    category="contract",
                    kind="debug-script-changed-during-coqtop",
                    message="Rocq debug script changed during coqtop execution",
                    repair="Restore the authorized script bytes and rerun coq-debug.",
                )
        except SystemExit as exc:
            post_failure = CoqBuildPlanError(
                category="contract",
                kind="debug-script-changed-during-coqtop",
                message=str(exc),
                repair="Restore the authorized script path and rerun coq-debug.",
            )
        except (OSError, ValueError) as exc:
            post_failure = CoqBuildPlanError(
                category="contract",
                kind="debug-script-changed-during-coqtop",
                message=str(exc) or repr(exc),
                repair="Restore the authorized script bytes and rerun coq-debug.",
            )
        response = {
            "status": "passed" if result["returncode"] == 0 else "failed",
            "tool": "coqtop",
            "kind": "coqtop_debug",
            "argv": argv,
            "cwd": str(build),
            "configured_coqtop": argv[0],
            "debug_script": debug_rel.as_posix(),
            "debug_script_path": str(debug_path),
            "debug_script_sha256": debug_digest,
            "debug_script_size": len(debug_payload),
            "load_argument": load_argument,
            "resolved_script_path": str(resolved_script),
            "resolved_matches_authorized": True,
            "source_goal_version": source_goal_version,
            "dependency_mode": "makefile-snapshot",
            "reused_base_vo_count": len(snapshot["base_artifacts"]),
            "preserved_build": bool(reuse_existing_build),
            **result,
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
        if post_failure is not None:
            response.update(
                {
                    "status": "failed",
                    "returncode": 2,
                    "first_failure": post_failure.first_failure(),
                    "stderr_tail": tail(
                        "\n".join(
                            item
                            for item in (
                                str(result.get("stderr_tail") or ""),
                                str(post_failure),
                            )
                            if item
                        )
                    ),
                }
            )
        return response
    except CoqBuildPlanError as exc:
        return {
            "status": "failed",
            "tool": "coqtop",
            "kind": "coqtop_debug",
            "debug_script": debug_rel.as_posix(),
            "source_goal_version": source_goal_version,
            "returncode": 2,
            "first_failure": exc.first_failure(),
            "stderr_tail": str(exc),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
    except (OSError, UnicodeError, ValueError) as exc:
        failure = CoqBuildPlanError(
            category="tooling",
            kind="coqtop-debug-preparation-failed",
            message=str(exc) or repr(exc),
            repair="Restore the accepted Makefile snapshot and fixed debug script.",
        )
        return {
            "status": "failed",
            "tool": "coqtop",
            "kind": "coqtop_debug",
            "debug_script": debug_rel.as_posix(),
            "source_goal_version": source_goal_version,
            "returncode": 2,
            "first_failure": failure.first_failure(),
            "stderr_tail": str(failure),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }


def audit_formal_case_lib_closure(
    *,
    workspace_root: Path,
    build_workspace: Path,
    formal_case_lib: Path,
    current_case_anchor: Path,
) -> dict[str, Any]:
    """Audit the final lib against the accepted source-only Makefile graph."""

    started = time.monotonic()
    root = workspace_root.expanduser().resolve()
    target = Path(formal_case_lib.as_posix())
    try:
        receipt = _receipt_from_run(
            workspace_root=root, build_workspace=build_workspace
        )
        snapshot = _require_validated_dune_snapshot(
            workspace_root=root,
            receipt=receipt,
        )
        identity = target_case_identity(target, case_anchor=current_case_anchor)
        expected = (Path(str(snapshot["case_directory"])), str(snapshot["case_name"]))
        if identity != expected or target != expected[0] / f"{expected[1]}_lib.v":
            raise CoqBuildPlanError(
                category="contract",
                kind="load-path-plan-mismatch",
                message="formal_case_lib audit target differs from the accepted case identity",
                repair="Use the persisted exact formal_case_lib path.",
            )
        text = _regular_file(root / target, label="formal_case_lib").read_text(encoding="utf-8")
        forbidden = {
            item
            for item in (Path(value) for value in snapshot["current_family"])
            if item != target
        }
        for module in _dependency_modules(text, source_label=target):
            dependency = _module_relative_for_source(
                module=module, source=target, snapshot=snapshot
            )
            if dependency in forbidden:
                raise CoqBuildPlanError(
                    category="contract",
                    kind="formal-case-lib-depends-on-generated-artifact",
                    message=(
                        "formal_case_lib reaches exact generated artifact "
                        + dependency.as_posix()
                    ),
                    repair="Remove the generated/current import from formal_case_lib.",
                )
        _validate_fixed_dependencies(snapshot=snapshot, source_texts={target: text})
        return {
            "status": "passed",
            "target_file": target.as_posix(),
            "dependency_mode": "makefile-snapshot",
            "dependency_digest": snapshot["dependency_digest"],
            "compiled": False,
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
    except CoqBuildPlanError as exc:
        return {
            "status": "failed",
            "target_file": target.as_posix(),
            "dependency_mode": "makefile-snapshot",
            "compiled": False,
            "first_failure": exc.first_failure(),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
