#!/usr/bin/env python3
"""Dune-prepared Rocq tooling for the verification controller.

Dependency discovery and stale base reconstruction have one owner: Dune.  An
accepted annotation is followed by one exact ``dune build`` whose generated
dependency data is sealed in the run.  Every proof, debug, parent, and final
check then compiles only the five possible current-case modules in a small
run-local directory and reads immutable base artifacts from ``_build/default``.

No second dependency resolver exists in the verification path. A proof-time
import that is not covered by the accepted Dune snapshot is rejected and must
be introduced by a new annotation round.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import stat
import time
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from atomic_file import atomic_copy_file, atomic_write_text
from file_integrity import sha256_bytes, sha256_text
from file_integrity import sha256_file as file_sha256
from path_utils import (
    fixed_path_under,
    path_is_link_like,
    run_root_from_path,
)
from process_adapter import run_bounded_process


COQ_COMMAND_TIMEOUT_SECONDS = 1800
DUNE_BUILD_TIMEOUT_SECONDS = 1800
DUNE_BUILD_DIRECTORY = Path("_build/default")
DUNE_SNAPSHOT_SCHEMA_VERSION = 1
DUNE_SNAPSHOT_FILE_NAME = "dune_dependency_snapshot.json"

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
SOURCE_SIDE_PRODUCT_SUFFIXES = COQ_SIDE_PRODUCT_SUFFIXES + (
    ".lia.cache",
    ".nia.cache",
    ".nra.cache",
)
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


def _configured_program(root: Path, tool: str) -> str:
    environment_names = {
        "coqc": "COQC_EXE",
        "coqtop": "COQTOP_EXE",
        "dune": "DUNE_EXE",
    }
    environment_value = os.environ.get(environment_names[tool], "").strip()
    if environment_value:
        return environment_value
    if tool == "dune" and os.name == "nt":
        shim = root / "dune.cmd"
        if shim.is_file():
            return str(shim)
    discovered = shutil.which(tool)
    return discovered or tool


def configured_coq_executable(workspace_root: Path, tool: str) -> str:
    if tool not in {"coqc", "coqtop"}:
        raise ValueError(f"unsupported Rocq tool: {tool}")
    return _configured_program(workspace_root.expanduser().resolve(), tool)


def configured_dune_executable(workspace_root: Path) -> str:
    return _configured_program(workspace_root.expanduser().resolve(), "dune")


def _base_load_path_entries(workspace_root: Path) -> tuple[CoqLoadPathEntry, ...]:
    root = workspace_root.expanduser().resolve()
    build_root = (root / DUNE_BUILD_DIRECTORY).resolve()
    return tuple(
        CoqLoadPathEntry(flag, build_root / physical, logical)
        for flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS
    )


def _render_load_path_flags(entries: Iterable[CoqLoadPathEntry]) -> list[str]:
    result: list[str] = []
    for entry in entries:
        if entry.flag not in {"-R", "-Q"} or not entry.physical.is_absolute():
            raise CoqBuildPlanError(
                category="contract",
                kind="load-path-plan-mismatch",
                message=f"invalid controller-owned Rocq load-path entry: {entry}",
                repair="Use the shared Dune-backed load-path renderer.",
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
    """Recognize installed modules absent from Dune's workspace dependency data.

    Rocq accepts many standard-library modules in historical unqualified form,
    including ``Lia`` and ``ZArith``. Qualified project imports still have to
    resolve to an artifact in the accepted snapshot.
    """

    return _is_standard_module(module) or "." not in module


def _dune_configuration_records(root: Path) -> list[dict[str, str]]:
    candidates = [root / "dune-project", root / "dune-workspace", root / "dune.cmd"]
    candidates.extend((root / "Rocq").rglob("dune"))
    records: list[dict[str, str]] = []
    for candidate in sorted(set(candidates), key=lambda item: item.as_posix()):
        if not (candidate.exists() or candidate.is_symlink()):
            continue
        _regular_file(candidate, label="Dune configuration")
        records.append(
            {
                "relative_path": candidate.relative_to(root).as_posix(),
                "sha256": file_sha256(candidate),
            }
        )
    if not any(item["relative_path"] == "dune-project" for item in records):
        raise CoqBuildPlanError(
            category="tooling",
            kind="dune-project-missing",
            message="repository dune-project is missing",
            repair="Restore the repository Dune configuration.",
        )
    return records


def _legacy_source_side_products(root: Path) -> tuple[list[Path], list[str]]:
    rocq_root = root / "Rocq"
    paths: list[Path] = []
    errors: list[str] = []
    if not rocq_root.is_dir():
        return paths, [f"Rocq source root is missing: {rocq_root}"]
    for candidate in rocq_root.rglob("*"):
        name = candidate.name
        is_aux = name.startswith(".") and name.endswith(".aux")
        is_suffix = any(name.endswith(suffix) for suffix in SOURCE_SIDE_PRODUCT_SUFFIXES)
        if not (is_aux or is_suffix):
            continue
        try:
            metadata = candidate.lstat()
        except FileNotFoundError:
            continue
        if path_is_link_like(candidate) or not stat.S_ISREG(metadata.st_mode):
            errors.append(f"legacy Coq side product is not a regular file: {candidate}")
        else:
            paths.append(candidate)
    return sorted(paths, key=lambda item: item.as_posix()), errors


def clean_legacy_source_side_products(workspace_root: Path) -> dict[str, Any]:
    """Remove obsolete source-tree Coq outputs that conflict with Dune rules."""

    root = workspace_root.expanduser().resolve()
    candidates, errors = _legacy_source_side_products(root)
    removed: list[str] = []
    if not errors:
        for candidate in candidates:
            candidate.unlink()
            removed.append(candidate.relative_to(root).as_posix())
    return {
        "status": "passed" if not errors else "failed",
        "removed_count": len(removed),
        "first_removed": removed[0] if removed else None,
        "error_count": len(errors),
        "first_error": errors[0] if errors else None,
    }


def _dependency_words(text: str) -> list[str]:
    """Split one Dune dependency-data field on unescaped whitespace.

    Dune may emit native Windows separators.  A backslash therefore remains a
    path separator unless it quotes whitespace; continuation newlines have
    already been removed by the caller.
    """

    words: list[str] = []
    current: list[str] = []
    index = 0
    while index < len(text):
        character = text[index]
        if character == "\\" and index + 1 < len(text) and text[index + 1].isspace():
            current.append(text[index + 1])
            index += 2
            continue
        if character.isspace():
            if current:
                words.append("".join(current))
                current = []
        else:
            current.append(character)
        index += 1
    if current:
        words.append("".join(current))
    return words


def _normalize_dune_dependency_token(token: str) -> str:
    """Remove only Make-style escaping from a leading Windows drive colon."""

    if (
        os.name == "nt"
        and len(token) >= 4
        and token[0].isascii()
        and token[0].isalpha()
        and token[1:3] == "\\:"
        and token[3] in "\\/"
    ):
        return token[0] + token[2:]
    return token


def _parse_dune_dependency_graph(
    *, workspace_root: Path
) -> dict[Path, tuple[Path, ...]]:
    root = workspace_root.expanduser().resolve()
    build_root = (root / DUNE_BUILD_DIRECTORY).resolve()
    graph: dict[Path, set[Path]] = {}
    dependency_files = sorted(
        build_root.rglob(".*.theory.d"), key=lambda item: item.as_posix()
    )
    if not dependency_files:
        raise CoqBuildPlanError(
            category="tooling",
            kind="dune-dependency-output-missing",
            message="Dune produced no Coq theory dependency data",
            repair="Repair the exact Dune target/configuration and rerun dune-build.",
        )
    for dependency_file in dependency_files:
        _regular_file(dependency_file, label="Dune theory dependency file")
        text = dependency_file.read_text(encoding="utf-8").replace("\\\r\n", " ").replace("\\\n", " ")
        for line in text.splitlines():
            delimiter = line.find(": ")
            if delimiter < 0:
                continue
            target_tokens = _dependency_words(line[:delimiter])
            dependency_tokens = _dependency_words(line[delimiter + 2 :])

            def build_relative(token: str) -> Path | None:
                token = _normalize_dune_dependency_token(token)
                candidate = Path(token.replace("\\", "/"))
                absolute = (
                    candidate.resolve()
                    if candidate.is_absolute()
                    else (dependency_file.parent / candidate).resolve()
                )
                try:
                    return absolute.relative_to(build_root)
                except ValueError:
                    return None

            targets = [
                relative
                for token in target_tokens
                if (relative := build_relative(token)) is not None
                and relative.suffix == ".vo"
            ]
            dependencies = {
                relative
                for token in dependency_tokens
                if (relative := build_relative(token)) is not None
                and relative.suffix == ".vo"
            }
            for target in targets:
                graph.setdefault(target, set()).update(dependencies)
    return {
        target: tuple(sorted(dependencies, key=lambda item: item.as_posix()))
        for target, dependencies in sorted(
            graph.items(), key=lambda item: item[0].as_posix()
        )
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
                kind="dune-dependency-cycle",
                message=f"Dune dependency data contains a cycle at {node.as_posix()}",
                repair="Repair the Rocq module dependency cycle and rerun dune-build.",
            )
        visiting.add(node)
        for dependency in graph.get(node, ()):
            visit(dependency)
        visiting.remove(node)
        visited.add(node)

    visit(target)
    return tuple(sorted(visited, key=lambda item: item.as_posix()))


def _snapshot_payload(
    *,
    workspace_root: Path,
    target_rel: Path,
    case_identity: tuple[Path, str],
    current_family: Sequence[Path],
    source_goal_version: str | None,
    dune_executable: str,
) -> dict[str, Any]:
    root = workspace_root.expanduser().resolve()
    build_root = (root / DUNE_BUILD_DIRECTORY).resolve()
    graph = _parse_dune_dependency_graph(workspace_root=root)
    target_artifact = target_rel.with_suffix(".vo")
    target_path = build_root / target_artifact
    _regular_file(target_path, label="exact Dune target artifact")
    if target_artifact not in graph:
        raise CoqBuildPlanError(
            category="tooling",
            kind="dune-target-not-in-dependency-data",
            message=(
                "exact Dune target is absent from generated dependency data: "
                + target_artifact.as_posix()
            ),
            repair="Ensure the target directory is covered by its Dune Coq theory.",
        )
    closure = _dependency_closure(graph, target_artifact)
    family_sources = {Path(item.as_posix()) for item in current_family}
    family_artifacts = {item.with_suffix(".vo") for item in family_sources}
    current_artifacts = set(closure) & family_artifacts
    base_artifacts = set(closure) - family_artifacts

    artifact_records: list[dict[str, str]] = []
    source_records: list[dict[str, str]] = []
    for artifact in sorted(base_artifacts, key=lambda item: item.as_posix()):
        artifact_path = _regular_file(
            build_root / artifact, label="Dune-prepared base artifact"
        )
        source = artifact.with_suffix(".v")
        source_path = _regular_file(root / source, label="Dune dependency source")
        artifact_records.append(
            {"relative_path": artifact.as_posix(), "sha256": file_sha256(artifact_path)}
        )
        source_records.append(
            {"relative_path": source.as_posix(), "sha256": file_sha256(source_path)}
        )

    dependency_records = [
        {
            "artifact": artifact.as_posix(),
            "requires": [
                dependency.as_posix()
                for dependency in graph.get(artifact, ())
                if dependency in closure
            ],
        }
        for artifact in closure
    ]
    current_dependencies = [
        {
            "source": artifact.with_suffix(".v").as_posix(),
            "requires": [
                dependency.with_suffix(".v").as_posix()
                for dependency in graph.get(artifact, ())
                if dependency in current_artifacts
            ],
        }
        for artifact in sorted(current_artifacts, key=lambda item: item.as_posix())
    ]
    configuration = _dune_configuration_records(root)
    directory, case_name = case_identity
    payload = {
        "schema_version": DUNE_SNAPSHOT_SCHEMA_VERSION,
        "source_goal_version": source_goal_version,
        "target": target_artifact.as_posix(),
        "build_root": DUNE_BUILD_DIRECTORY.as_posix(),
        "dune_executable": dune_executable,
        "case_directory": directory.as_posix(),
        "case_name": case_name,
        "current_family": [item.as_posix() for item in current_family],
        "current_sources": [
            item.with_suffix(".v").as_posix()
            for item in sorted(current_artifacts, key=lambda value: value.as_posix())
        ],
        "current_dependencies": current_dependencies,
        "dependencies": dependency_records,
        "base_sources": source_records,
        "base_artifacts": artifact_records,
        "configuration": configuration,
    }
    payload["dependency_digest"] = _stable_digest(dependency_records)
    payload["source_digest"] = _stable_digest(source_records)
    payload["artifact_digest"] = _stable_digest(artifact_records)
    payload["configuration_digest"] = _stable_digest(configuration)
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
    """Run one exact Dune build and seal its dependency/artifact snapshot."""

    started = time.monotonic()
    timeout = float(
        DUNE_BUILD_TIMEOUT_SECONDS if timeout_seconds is None else timeout_seconds
    )
    root = workspace_root.expanduser().resolve()
    try:
        target_rel = _repository_relative(target_file, root, label="Dune target")
        anchor = _repository_relative(
            current_case_anchor, root, label="current-case anchor"
        )
        identity = target_case_identity(target_rel, case_anchor=anchor)
        if identity is None:
            raise CoqBuildPlanError(
                category="contract",
                kind="load-path-plan-mismatch",
                message="Dune build lacks one authoritative current-case identity",
                repair="Restore the persisted target_files case anchor.",
            )
        family = target_case_sources(target_rel, case_anchor=anchor)
        if target_rel not in family:
            raise CoqBuildPlanError(
                category="contract",
                kind="dune-target-boundary",
                message=f"Dune target is outside the exact current family: {target_rel}",
                repair="Build only the persisted formal_case_lib or goal_check target.",
            )
        _regular_file(root / target_rel, label="Dune target source")
        cleanup = clean_legacy_source_side_products(root)
        if cleanup["status"] != "passed":
            return _dune_failure(
                target=target_rel,
                started=started,
                kind="legacy-side-product-cleanup",
                message=str(cleanup["first_error"]),
                repair="Restore ordinary source-tree paths, then rerun the same Dune build.",
                legacy_cleanup=cleanup,
            )
        dune = configured_dune_executable(root)
        target_artifact = target_rel.with_suffix(".vo")
        argv = [
            dune,
            "build",
            "--root",
            str(root),
            "--display=short",
            target_artifact.as_posix(),
        ]
        process = run_bounded_process(
            argv,
            cwd=root,
            timeout_seconds=timeout,
            timeout_message=(
                f"\nDune build timed out after "
                f"{timeout:g} seconds."
            ),
            detached_pipe_message="\nDune cleanup could not fully drain a detached pipe.",
            launch_error_prefix="cannot launch Dune: ",
        )
        combined = "\n".join(item for item in (process.stdout, process.stderr) if item)
        if process.returncode != 0:
            return _dune_failure(
                target=target_rel,
                started=started,
                kind="dune-build-failed",
                message=(
                    tail(process.stderr or process.stdout)
                    or "Dune failed without diagnostic output"
                ),
                repair="Repair the first Dune/Rocq diagnostic and rerun the unchanged action.",
                returncode=process.returncode,
                argv=argv,
                stdout_tail=tail(process.stdout),
                stderr_tail=tail(process.stderr),
                first_diagnostic=extract_first_coq_failure(combined),
                legacy_cleanup=cleanup,
            )
        payload = _snapshot_payload(
            workspace_root=root,
            target_rel=target_rel,
            case_identity=identity,
            current_family=family,
            source_goal_version=source_goal_version,
            dune_executable=dune,
        )
        receipt: dict[str, Any] = {
            "status": "passed",
            "source_goal_version": source_goal_version,
            "target": target_artifact.as_posix(),
            "build_root": DUNE_BUILD_DIRECTORY.as_posix(),
            "dune_executable": dune,
            "dependency_digest": payload["dependency_digest"],
            "source_digest": payload["source_digest"],
            "artifact_digest": payload["artifact_digest"],
            "configuration_digest": payload["configuration_digest"],
            "base_artifact_count": len(payload["base_artifacts"]),
            "current_source_count": len(payload["current_sources"]),
            "rebuilt_count": sum(
                1 for line in combined.splitlines() if re.match(r"^\s*coqc\s", line)
            ),
            "returncode": 0,
            "legacy_cleanup": cleanup,
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
        if snapshot_path is None:
            receipt["_snapshot"] = payload
        else:
            snapshot = fixed_path_under(
                snapshot_path,
                root,
                label="run Dune dependency snapshot",
            )
            atomic_write_text(
                snapshot,
                json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
                suffix=".dune-snapshot",
            )
            receipt["snapshot"] = snapshot.relative_to(root).as_posix()
            receipt["snapshot_sha256"] = file_sha256(snapshot)
        return receipt
    except CoqBuildPlanError as exc:
        return {
            "status": "failed",
            "returncode": 2,
            "first_failure": exc.first_failure(),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return _dune_failure(
            target=Path(target_file.as_posix()),
            started=started,
            kind="dune-preparation-failed",
            message=str(exc) or repr(exc),
            repair="Restore readable Dune configuration, sources, and build output.",
        )


def compact_dune_preparation(evidence: Mapping[str, Any]) -> dict[str, Any]:
    keys = (
        "status",
        "source_goal_version",
        "target",
        "build_root",
        "dune_executable",
        "snapshot",
        "snapshot_sha256",
        "dependency_digest",
        "source_digest",
        "artifact_digest",
        "configuration_digest",
        "base_artifact_count",
        "current_source_count",
        "rebuilt_count",
        "returncode",
        "legacy_cleanup",
        "elapsed_seconds",
        "first_failure",
    )
    return {key: evidence[key] for key in keys if key in evidence}


def _strict_snapshot(payload: Any) -> dict[str, Any]:
    if not isinstance(payload, dict):
        raise CoqBuildPlanError(
            category="contract",
            kind="dune-snapshot-invalid",
            message="Dune dependency snapshot is not a JSON object",
            repair="Rerun the controller-owned dune-build action.",
        )
    required = {
        "schema_version",
        "source_goal_version",
        "target",
        "build_root",
        "dune_executable",
        "case_directory",
        "case_name",
        "current_family",
        "current_sources",
        "current_dependencies",
        "dependencies",
        "base_sources",
        "base_artifacts",
        "configuration",
        "dependency_digest",
        "source_digest",
        "artifact_digest",
        "configuration_digest",
    }
    if set(payload) != required or payload.get("schema_version") != DUNE_SNAPSHOT_SCHEMA_VERSION:
        raise CoqBuildPlanError(
            category="contract",
            kind="dune-snapshot-invalid",
            message="Dune dependency snapshot fields or schema version are invalid",
            repair="Rerun the controller-owned dune-build action.",
        )
    return payload


def _load_snapshot_from_receipt(
    *, workspace_root: Path, receipt: Mapping[str, Any]
) -> dict[str, Any]:
    root = workspace_root.expanduser().resolve()
    embedded = receipt.get("_snapshot")
    if embedded is not None:
        return _strict_snapshot(embedded)
    relative = Path(str(receipt.get("snapshot") or ""))
    if relative.is_absolute() or ".." in relative.parts or not relative.parts:
        raise CoqBuildPlanError(
            category="contract",
            kind="dune-snapshot-path",
            message="Dune preparation snapshot path is invalid",
            repair="Rerun the controller-owned dune-build action.",
        )
    path = fixed_path_under(root / relative, root, label="Dune dependency snapshot")
    _regular_file(path, label="Dune dependency snapshot")
    expected_digest = str(receipt.get("snapshot_sha256") or "")
    raw = path.read_bytes()
    if not expected_digest or sha256_bytes(raw) != expected_digest:
        raise CoqBuildPlanError(
            category="freshness",
            kind="dune-snapshot-drift",
            message="Dune dependency snapshot bytes changed after preparation",
            repair="Rerun the controller-owned dune-build action.",
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
    if not isinstance(receipt, Mapping) or receipt.get("status") != "passed":
        raise ValueError("accepted Dune preparation is missing")
    snapshot = _load_snapshot_from_receipt(
        workspace_root=root, receipt=receipt
    )
    if (
        expected_source_goal_version is not None
        and snapshot.get("source_goal_version") != expected_source_goal_version
    ):
        raise ValueError("Dune preparation source_goal_version is stale")
    digest_fields = {
        "dependency_digest": snapshot["dependencies"],
        "source_digest": snapshot["base_sources"],
        "artifact_digest": snapshot["base_artifacts"],
        "configuration_digest": snapshot["configuration"],
    }
    for field, value in digest_fields.items():
        if (
            snapshot.get(field) != _stable_digest(value)
            or receipt.get(field) != snapshot.get(field)
        ):
            raise ValueError(f"Dune preparation {field} is invalid")
    if _dune_configuration_records(root) != snapshot["configuration"]:
        raise ValueError("Dune configuration changed after preparation")
    build_root = root / Path(str(snapshot["build_root"]))
    for record in snapshot["base_sources"]:
        path = root / Path(str(record["relative_path"]))
        _regular_file(path, label="Dune dependency source")
        if file_sha256(path) != record["sha256"]:
            raise ValueError(
                f"Dune dependency source changed: {record['relative_path']}"
            )
    for record in snapshot["base_artifacts"]:
        path = build_root / Path(str(record["relative_path"]))
        _regular_file(path, label="Dune-prepared base artifact")
        if file_sha256(path) != record["sha256"]:
            raise ValueError(
                f"Dune-prepared base artifact changed: {record['relative_path']}"
            )
    return snapshot


def _require_validated_dune_snapshot(
    *,
    workspace_root: Path,
    receipt: Mapping[str, Any] | None,
    expected_source_goal_version: str | None = None,
    repair: str = "Rerun the controller-owned dune-build action.",
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
            kind="dune-preparation-stale",
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
    build_workspace: Path,
) -> dict[str, Any]:
    receipt = _receipt_from_run(
        workspace_root=workspace_root, build_workspace=build_workspace
    )
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
                    kind="dune-dependency-not-prepared",
                    message=(
                        f"proof-time import {module} in {source.as_posix()} is not "
                        "present in the accepted Dune dependency snapshot"
                    ),
                    repair=(
                        "Return to annotation, add the required import there, and "
                        "accept a new Dune snapshot before proving."
                    ),
                )
            if dependency not in allowed:
                raise CoqBuildPlanError(
                    category="tooling",
                    kind="dune-dependency-not-prepared",
                    message=(
                        f"proof-time dependency is outside the accepted Dune snapshot: "
                        f"{dependency.as_posix()}"
                    ),
                    repair="Return to annotation and rebuild the fixed Dune dependency snapshot.",
                )
            if source in fixed_edges and dependency in current and dependency not in fixed_edges[source]:
                raise CoqBuildPlanError(
                    category="contract",
                    kind="current-dependency-changed-after-annotation",
                    message=(
                        f"current dependency edge changed after annotation: "
                        f"{source.as_posix()} -> {dependency.as_posix()}"
                    ),
                    repair="Return to annotation so Dune can accept the new dependency graph.",
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
            repair="Keep the formal directory under a configured Dune Coq theory root.",
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
        "dependency_mode": "dune-snapshot",
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
    """Compile/check current files using one previously sealed Dune graph."""

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
                    "Rerun the controller-owned dune-build action before proving."
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
                    kind="dune-preparation-stale",
                    message="Dune preparation source_goal_version is stale",
                    repair=(
                        "Rerun the controller-owned dune-build action before proving."
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
                message="check target identity differs from the accepted Dune snapshot",
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
                "dependency_mode": "dune-snapshot",
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
                    "dependency_mode": "dune-snapshot",
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
            "dependency_mode": "dune-snapshot",
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
                repair="Restore the accepted Dune snapshot and fixed current files.",
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
                    kind="dune-preparation-stale",
                    message="Dune preparation source_goal_version is stale",
                    repair="Rerun the controller-owned dune-build action.",
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
            "dependency_mode": "dune-snapshot",
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
            repair="Restore the accepted Dune snapshot and fixed debug script.",
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
    """Audit the final lib against the accepted, source-only Dune graph."""

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
            "dependency_mode": "dune-snapshot",
            "dependency_digest": snapshot["dependency_digest"],
            "compiled": False,
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
    except CoqBuildPlanError as exc:
        return {
            "status": "failed",
            "target_file": target.as_posix(),
            "dependency_mode": "dune-snapshot",
            "compiled": False,
            "first_failure": exc.first_failure(),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }
