"""One dependency-plan, staging, and Rocq execution flow for both native backends."""

from __future__ import annotations

import json
import math
import os
import re
import stat
import time
from collections.abc import Iterable, Mapping, Sequence
from pathlib import Path
from typing import Any

from atomic_file import atomic_write_text
from file_integrity import _lexical_regular_file_snapshot, _snapshot_text
from path_utils import fixed_path_under, path_is_link_like, run_root_from_path
from process_adapter import run_bounded_process, tool_progress


COQ_COMMAND_TIMEOUT_SECONDS = 15 * 60


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


class CoqBuildPlanError(ValueError):
    """Structured native-preparation or Rocq failure returned to the controller."""

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


def _repository_relative(path: Path, root: Path, *, label: str) -> Path:
    raw = Path(path.as_posix())
    if raw.is_absolute():
        try:
            raw = fixed_path_under(path, root, label=label).relative_to(root.absolute())
        except ValueError as exc:
            raise CoqBuildPlanError(
                category="contract",
                kind="path-boundary",
                message=f"{label} escaped the repository: {path}",
                repair="Use the controller-persisted repository-relative target path.",
            ) from exc
    if raw.drive or raw.root or ".." in raw.parts:
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


def _logical_root_for_relative(relative: Path) -> tuple[Path, str, str] | None:
    normalized = Path(relative.as_posix())
    for flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS:
        physical_root = Path(physical)
        if normalized.is_relative_to(physical_root):
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


MODULE_PATTERN = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
REQUIRE_RE = re.compile(
    rf"\b(?:From\s+(?P<prefix>{MODULE_PATTERN})\s+)?Require\s+"
    rf"(?:(?:Import|Export)\s+)?(?P<modules>{MODULE_PATTERN}(?:\s+{MODULE_PATTERN})*)\s*\.(?=\s|$)",
    re.MULTILINE,
)


def _required_modules(text: str) -> list[str]:
    modules: list[str] = []
    for match in REQUIRE_RE.finditer(text):
        prefix = match.group("prefix")
        modules.extend(
            f"{prefix}.{token}" if prefix else token
            for token in match.group("modules").split()
        )
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


def _normalized_overlay_map(
    overlays: Mapping[Path, Path] | None,
) -> dict[Path, Path]:
    result: dict[Path, Path] = {}
    for raw_destination, raw_source in (overlays or {}).items():
        destination = Path(raw_destination.as_posix())
        source = raw_source.expanduser().absolute()
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


def _path_spellings(path: Path) -> set[str]:
    text = str(path)
    values = {text, text.replace("/", "\\"), text.replace("\\", "/")}
    if text.endswith(".v"):
        stem = text[:-2]
        values.update({stem, stem.replace("/", "\\"), stem.replace("\\", "/")})
    return values


def normalize_current_source_texts(
    *,
    workspace_root: Path,
    build_workspace: Path,
    texts: Mapping[Path, str],
    sources: Iterable[Path],
) -> dict[Path, str]:
    """Normalize generated import spellings without changing comments or strings."""

    root = workspace_root.expanduser().resolve()
    build = build_workspace.expanduser().absolute()
    texts = {relative: text.replace("\r\n", "\n") for relative, text in texts.items()}
    replacements: dict[str, str] = {}
    local: dict[Path, dict[str, str]] = {}
    for relative in sources:
        for spelling in _path_spellings(root / relative) | _path_spellings(build / relative):
            replacements[spelling] = relative.stem
        replacements[relative.with_suffix("").as_posix()] = relative.stem
        logical = relative_to_logical_module(relative)
        if logical:
            local.setdefault(relative.parent, {})[relative.stem] = logical
    path_pattern = re.compile("|".join(
        re.escape(value) for value in sorted(replacements, key=len, reverse=True)
    )) if replacements else None
    for relative, original in texts.items():
        text = original
        if path_pattern is not None:
            for match in reversed(list(path_pattern.finditer(_strip_comments_and_strings(text)))):
                text = text[:match.start()] + replacements[match.group()] + text[match.end():]
        for module in _dependency_modules(text, source_label=relative):
            sibling = relative.parent / f"{module}.v"
            logical = relative_to_logical_module(sibling)
            if "." not in module and logical and (root / sibling).is_file():
                local.setdefault(relative.parent, {})[module] = logical
        texts[relative] = text
    for relative, text in texts.items():
        mapping = local.get(relative.parent, {})
        code = _strip_comments_and_strings(text)
        edits: list[tuple[int, int, str]] = []
        for command in REQUIRE_RE.finditer(code):
            if command.group("prefix"):
                continue
            for match in re.finditer(MODULE_PATTERN, command.group("modules")):
                replacement = mapping.get(match.group())
                if replacement:
                    start = command.start("modules") + match.start()
                    edits.append((start, start + len(match.group()), replacement))
        for start, end, replacement in reversed(edits):
            text = text[:start] + replacement + text[end:]
        texts[relative] = text
    return texts


def stage_current_sources(
    *,
    workspace_root: Path,
    build_workspace: Path,
    sources: Mapping[Path, Path],
) -> tuple[dict[Path, str], list[str]]:
    """Normalize the exact source batch in memory, then write changed bytes once."""

    root = workspace_root.expanduser().resolve()
    build = fixed_path_under(build_workspace, root, label="current staging directory")
    texts: dict[Path, str] = {}
    for relative, source in sources.items():
        if relative.is_absolute() or relative.drive or ".." in relative.parts:
            raise ValueError(f"current stage destination must be relative: {relative}")
        try:
            source_relative = source.relative_to(root).as_posix()
        except ValueError as exc:
            raise CoqBuildPlanError(category="contract", kind="source-stage-boundary", message=str(exc),
                                    repair="Use controller-owned sources within the main root.") from exc
        snapshot = _lexical_regular_file_snapshot(root=root, relative=source_relative, label="current source")
        texts[relative] = _snapshot_text(snapshot, label="current source").replace("\r\n", "\n")
    texts = normalize_current_source_texts(
        workspace_root=root, build_workspace=build, texts=texts, sources=sources,
    )
    for auto_rel, auto_text in texts.items():
        if not auto_rel.name.endswith("_proof_auto.v"):
            continue
        manual_rel = auto_rel.with_name(auto_rel.name.replace("_proof_auto.v", "_proof_manual.v"))
        if manual_rel not in texts:
            continue
        manual_names = {
            match.group(2)
            for match in PROOF_DECLARATION_RE.finditer(_strip_comments_and_strings(texts[manual_rel]))
        }
        for match in reversed(list(PROOF_BLOCK_RE.finditer(_strip_comments_and_strings(auto_text)))):
            if match.group(1) in manual_names:
                auto_text = auto_text[:match.start()] + auto_text[match.end():]
        texts[auto_rel] = auto_text
    changed: list[str] = []
    for relative, text in texts.items():
        destination = build / relative
        snapshot = _lexical_regular_file_snapshot(root=build, relative=relative.as_posix(), label="staged current source")
        if snapshot["state"] not in {"present", "missing"}:
            raise ValueError(f"invalid staged current source {relative}: {snapshot.get('message')}")
        if snapshot.get("data") == text.encode("utf-8"):
            continue
        destination.parent.mkdir(parents=True, exist_ok=True)
        atomic_write_text(destination, text, suffix=".stage")
        changed.append(relative.as_posix())
    return texts, changed


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


def fixed_source(root: Path, relative: Path, *, label: str = "source") -> Path:
    """Validate one repository file before any tool reads it."""
    try:
        path = fixed_path_under(root / relative, root, label=label)
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    return _regular_file(path, label=label)


def dependency_closure(
    graph: Mapping[Path, Sequence[Path]], roots: Iterable[Path],
) -> list[Path]:
    """Return dependencies before consumers, rejecting missing nodes and cycles."""
    order: list[Path] = []
    active: set[Path] = set()
    visited: set[Path] = set()

    def visit(source: Path) -> None:
        if source in visited:
            return
        if source in active:
            raise ValueError(f"Rocq dependency cycle at {source}")
        if source not in graph:
            raise ValueError(f"Rocq dependency graph omits {source}")
        active.add(source)
        for dependency in graph[source]:
            visit(dependency)
        active.remove(source)
        visited.add(source)
        order.append(source)

    for source in sorted(set(roots)):
        visit(source)
    return order


def command_deadline(timeout_seconds: int | float | None) -> float:
    timeout = COQ_COMMAND_TIMEOUT_SECONDS if timeout_seconds is None else float(timeout_seconds)
    if not math.isfinite(timeout) or timeout < 0:
        raise ValueError("Coq timeout must be finite and non-negative")
    return time.monotonic() + min(timeout, COQ_COMMAND_TIMEOUT_SECONDS)


def run_tool(
    argv: Sequence[str], *, cwd: Path, deadline: float, label: str,
    environment: Mapping[str, str] | None = None,
):
    """All native preparation and Rocq processes spend the same command budget."""
    result = run_bounded_process(
        argv, cwd=cwd, timeout_seconds=max(0.0, deadline - time.monotonic()),
        environment=environment, timeout_message=f"\n{label} exhausted the command budget.",
        detached_pipe_message="\nDetached descendants retained output pipes.",
        launch_error_prefix=f"Cannot launch {label}: ", progress_callback=tool_progress(label),
    )
    if result.returncode:
        diagnostic = extract_first_coq_failure(result.stderr + "\n" + result.stdout)
        raise CoqBuildPlanError(
            category="tooling" if result.returncode in {124, 127} else "verification",
            kind="tool-timeout" if result.returncode == 124 else "tool-failed",
            message=(diagnostic or {}).get("message") or tail(result.stderr or result.stdout)
                    or f"{label} exited with {result.returncode}",
            repair="Inspect the reported native tool failure and retry the same command.",
            evidence={"returncode": result.returncode, "argv": list(argv),
                      "stdout_tail": tail(result.stdout), "stderr_tail": tail(result.stderr),
                      "first_diagnostic": diagnostic},
        )
    return result


def failure_result(error: Exception, started: float, **context: Any) -> dict[str, Any]:
    failure = error if isinstance(error, CoqBuildPlanError) else CoqBuildPlanError(
        category="tooling", kind="preparation-failed", message=str(error),
        repair="Restore the reported source, path, or native build configuration.",
    )
    return {**context, "status": "failed", "returncode": failure.evidence.get("returncode", 2),
            "first_failure": failure.first_failure(), "stderr_tail": str(failure),
            "elapsed_seconds": round(time.monotonic() - started, 6)}


def _case_family(anchor: Path) -> tuple[Path, str, set[Path]]:
    identity = _canonical_target_case_identity(anchor)
    if identity is None:
        raise ValueError(f"Invalid current-case anchor: {anchor}")
    directory, name = identity
    if relative_to_logical_module(anchor) is None:
        raise ValueError(f"No Rocq load path covers {anchor}")
    return directory, name, {directory / f"{name}{suffix}" for suffix in TARGET_CASE_MODULE_SUFFIXES}


def _present_family(root: Path, family: set[Path]) -> list[Path]:
    present = []
    for source in sorted(family):
        path = fixed_path_under(root / source, root, label="current source")
        if os.path.lexists(path):
            fixed_source(root, source)
            present.append(source)
    return present


def prepare_plan(
    backend: Any, *, root: Path, target: Path, anchor: Path,
    deadline: float, all_current: bool = False,
) -> dict[str, Any]:
    """Prepare one native graph; the family alone determines current versus base."""
    _directory, _name, family = _case_family(anchor)
    if target not in family:
        raise ValueError(f"Dependency target is outside the current family: {target}")
    fixed_source(root, target)
    targets = _present_family(root, family) if all_current else [target]
    remove_target_case_side_products(root, family)
    graph = backend.prepare_native(root=root, targets=targets, family=family, deadline=deadline)
    dependency_closure(graph, targets)
    return {"build_mode": backend.BUILD_MODE, "target": target.with_suffix(".vo").as_posix(),
            "case_anchor": anchor.as_posix(),
            "dependencies": {source.as_posix(): [path.as_posix() for path in dependencies]
                             for source, dependencies in sorted(graph.items())}}


def plan_graph(plan: Mapping[str, Any]) -> dict[Path, tuple[Path, ...]]:
    return {Path(source): tuple(Path(value) for value in dependencies)
            for source, dependencies in plan["dependencies"].items()}


def _plan_relative(value: Any, suffix: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ValueError("Dependency paths must be non-empty strings")
    path = Path(value)
    if (path.is_absolute() or path.drive or path.root or ".." in path.parts
            or "\\" in value or path.as_posix() != value or path.suffix != suffix):
        raise ValueError(f"Invalid dependency path: {value}")
    return path


def validate_plan(root: Path, backend: Any, plan: Any) -> dict[str, Any]:
    """Check the one persisted input boundary, without redundant derived records."""
    if not isinstance(plan, dict) or set(plan) != {"build_mode", "target", "case_anchor", "dependencies"}:
        raise ValueError("Invalid dependency plan fields")
    if plan["build_mode"] != backend.BUILD_MODE:
        raise ValueError("Dependency plan backend differs from the current workspace")
    target = _plan_relative(plan["target"], ".vo").with_suffix(".v")
    anchor = _plan_relative(plan["case_anchor"], ".v")
    _directory, _name, family = _case_family(anchor)
    if target not in family or not isinstance(plan["dependencies"], dict):
        raise ValueError("Invalid dependency plan target or graph")
    graph = {}
    for source, dependencies in plan["dependencies"].items():
        if not isinstance(dependencies, list):
            raise ValueError(f"Invalid dependencies for {source}")
        graph[_plan_relative(source, ".v")] = tuple(_plan_relative(value, ".v") for value in dependencies)
    if target not in graph:
        raise ValueError("Dependency plan omits its target")
    if set(dependency_closure(graph, set(graph) & family)) != set(graph):
        raise ValueError("Dependency plan contains sources outside the current-family closure")
    base_root = root / "_build/default" if backend.BUILD_MODE == "dune" else root
    for source in graph:
        fixed_source(root, source)
        if source not in family:
            if set(graph[source]) & family:
                raise ValueError(f"Base module depends on the current case: {source}")
            fixed_source(base_root, source.with_suffix(".vo"), label="base artifact")
    return plan


def load_plan(root: Path, backend: Any, receipt: Mapping[str, Any] | None) -> dict[str, Any]:
    if not isinstance(receipt, Mapping) or receipt.get("status") != "passed" or receipt.get("returncode") != 0:
        raise ValueError("Successful native dependency preparation is missing")
    if "_plan" in receipt:
        plan = receipt["_plan"]
    else:
        relative = _plan_relative(receipt.get("snapshot"), ".json")
        plan = json.loads(fixed_source(root, relative, label="dependency plan").read_text(encoding="utf-8"))
    return validate_plan(root, backend, plan)


def preparation_receipt(plan: dict[str, Any], started: float, deadline: float) -> dict[str, Any]:
    _directory, _name, family = _case_family(Path(plan["case_anchor"]))
    sources = set(plan_graph(plan))
    return {"status": "passed", "returncode": 0, "build_mode": plan["build_mode"],
            "target": plan["target"], "base_artifact_count": len(sources - family),
            "current_source_count": len(sources & family), "_plan": plan, "_deadline": deadline,
            "elapsed_seconds": round(time.monotonic() - started, 6)}


def _resolve_import(module: str, source: Path, known: set[Path]) -> Path | None:
    mapped = logical_module_to_relative(module)
    if mapped is not None:
        return mapped
    if _is_standard_module(module):
        return None
    if "." not in module:
        sibling = source.parent / f"{module}.v"
        if sibling in known:
            return sibling
        matches = [path for path in known if path.stem == module]
        if len(matches) > 1:
            raise ValueError(f"Ambiguous import {module} in {source}; use its logical path")
        return matches[0] if matches else None  # Installed unqualified standard modules.
    raise ValueError(f"Import {module} in {source} is outside the prepared dependency graph")


def current_graph(plan: Mapping[str, Any], texts: Mapping[Path, str]) -> dict[Path, tuple[Path, ...]]:
    known = set(plan_graph(plan))
    result = {}
    for source, text in texts.items():
        dependencies = set()
        for module in _dependency_modules(text, source_label=source):
            dependency = _resolve_import(module, source, known)
            if dependency is not None and dependency not in known:
                raise ValueError(f"Import {module} in {source} is outside the prepared dependency graph")
            if dependency in texts:
                dependencies.add(dependency)
        result[source] = tuple(sorted(dependencies))
    return result


def coq_argv(backend: Any, root: Path, build: Path, directory: Path, target: Path, *, debug: bool = False) -> list[str]:
    logical = relative_to_logical_module(directory / "__marker__.v")
    if logical is None:
        raise ValueError(f"No logical load path for {directory}")
    entries = [*backend.base_load_paths(root), ("-R", build / directory, logical.rsplit(".", 1)[0])]
    flags = [token for flag, path, logical in entries for token in (flag, str(path), logical)]
    tool = "coqtop" if debug else "coqc"
    return [backend.configured_program(root, tool), "-q", *(["-batch"] if debug else []),
            *flags, *(["-l"] if debug else []), str(target)]


def _check_context(
    backend: Any, *, root: Path, build: Path, anchor: Path, target: Path,
    deadline: float, library_only: bool, preparation: Mapping[str, Any] | None,
    overlays: Mapping[Path, Path] | None,
) -> tuple[dict[str, Any], dict[Path, str], Path]:
    layout = build_workspace_layout_error(root, build)
    if layout:
        raise ValueError(layout)
    directory, name, family = _case_family(anchor)
    if preparation is None:
        native_target = target if target in family else anchor
        plan = prepare_plan(backend, root=root, target=native_target, anchor=anchor,
                            deadline=deadline, all_current=not library_only)
    else:
        plan = load_plan(root, backend, preparation)
        if _case_family(Path(plan["case_anchor"])) != (directory, name, family):
            raise ValueError("Dependency preparation belongs to a different current case")
    overlay_map = _normalized_overlay_map(overlays)
    if set(overlay_map) - family:
        raise ValueError("Overlay destinations must belong to the current case")
    sources = set(plan_graph(plan)) & family
    build.mkdir(parents=True, exist_ok=True)
    texts, _changed = stage_current_sources(workspace_root=root, build_workspace=build,
        sources={source: overlay_map.get(source, root / source) for source in sources})
    return plan, texts, directory / f"{name}_lib.v"


def _compile(backend: Any, root: Path, build: Path, directory: Path, order: Iterable[Path], deadline: float) -> list[str]:
    compiled = []
    for source in order:
        remove_target_case_side_products(build, [source])
        run_tool(coq_argv(backend, root, build, directory, source), cwd=build,
                 deadline=deadline, label=f"Rocq {source}")
        fixed_source(build, source.with_suffix(".vo"), label="compiled current artifact")
        compiled.append(source.as_posix())
    return compiled


def _group_wrapper(build: Path, target: Path, directory: Path, config: Mapping[str, Any]) -> list[Path]:
    modules = config.get("require_modules")
    witnesses = config.get("assigned_witnesses")
    theory = config.get("case_theory")
    identifier = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
    if (target.parent != directory or not isinstance(modules, list) or not modules
            or not isinstance(witnesses, list) or not witnesses
            or any(not isinstance(value, str) or not identifier.fullmatch(value) for value in modules + witnesses)
            or theory != relative_to_logical_module(directory / "__marker__.v").rsplit(".", 1)[0]):
        raise ValueError("Invalid controller group-check wrapper assignment")
    path = fixed_path_under(build / target, build, label="group wrapper")
    atomic_write_text(path, f"From {theory} Require Import {' '.join(modules)}.\n"
                      + "\n".join(f"Check {name}." for name in witnesses) + "\n")
    return [directory / f"{module}.v" for module in modules]


def run_coqc_check(
    backend: Any, *, workspace_root: Path, build_workspace: Path, target_file: Path,
    target_kind: str, timeout_seconds: int | float | None = None,
    group_check: Mapping[str, Any] | None = None, overlays: Mapping[Path, Path] | None = None,
    incremental: bool = False, current_case_anchor: Path | None = None,
    dune_preparation: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    started = time.monotonic()
    context = {"target_file": target_file.as_posix(), "target_kind": target_kind,
               "build_workspace": str(build_workspace), "dependency_mode": backend.BUILD_MODE}
    try:
        deadline = command_deadline(timeout_seconds)
        if dune_preparation and "_deadline" in dune_preparation:
            deadline = min(deadline, float(dune_preparation["_deadline"]))
        root = fixed_path_under(workspace_root.expanduser().absolute(), workspace_root.expanduser().absolute(), label="workspace")
        build = build_workspace.expanduser().absolute()
        target = _repository_relative(target_file, root, label="Coq target")
        anchor = _repository_relative(current_case_anchor or target, root, label="case anchor")
        library_only = target_kind in {"formal-case-lib", "formal-case-lib-design"}
        plan, texts, library = _check_context(backend, root=root, build=build, anchor=anchor,
            target=target, deadline=deadline, library_only=library_only,
            preparation=dune_preparation, overlays=overlays)
        graph = current_graph(plan, texts)
        if target_kind == "group-check":
            roots = _group_wrapper(build, target, library.parent, group_check or {})
        elif incremental or library_only:
            roots = [target]
        else:
            roots = list(graph)
        if library in graph and library not in roots:
            roots.append(library)
        order = dependency_closure(graph, roots)
        if target_kind == "group-check":
            order.append(target)
        elif target not in order:
            raise ValueError(f"Check target was not selected for compilation: {target}")
        compiled = _compile(backend, root, build, library.parent, order, deadline)
        return {**context, "status": "passed", "returncode": 0,
                "recompiled_target_files": compiled, "staged_current_source_count": len(texts),
                "reused_base_vo_count": len(plan_graph(plan)) - len(texts),
                "elapsed_seconds": round(time.monotonic() - started, 6)}
    except (CoqBuildPlanError, OSError, UnicodeError, ValueError) as exc:
        return failure_result(exc, started, **context)


def run_coqtop_debug(
    backend: Any, *, workspace_root: Path, build_workspace: Path, debug_script: Path,
    timeout_seconds: int | float | None = None, overlays: Mapping[Path, Path] | None = None,
    current_case_anchor: Path | None = None,
) -> dict[str, Any]:
    started = time.monotonic()
    context = {"tool": "coqtop", "kind": "coqtop_debug", "debug_script": debug_script.as_posix()}
    try:
        if current_case_anchor is None:
            raise ValueError("Debug requires the controller's current-case anchor")
        deadline = command_deadline(timeout_seconds)
        root = fixed_path_under(workspace_root.expanduser().absolute(), workspace_root.expanduser().absolute(), label="workspace")
        build = build_workspace.expanduser().absolute()
        anchor = _repository_relative(current_case_anchor, root, label="case anchor")
        plan, texts, library = _check_context(backend, root=root, build=build, anchor=anchor,
            target=anchor, deadline=deadline, library_only=False, preparation=None, overlays=overlays)
        graph = current_graph(plan, texts)
        roots = [source for source in graph if not source.name.endswith("_goal_check.v")]
        _compile(backend, root, build, library.parent, dependency_closure(graph, roots), deadline)
        script = fixed_source(build, _plan_relative(debug_script.as_posix(), ".v"), label="debug script")
        payload = script.read_bytes()
        # Check imports against the same prepared graph before loading the script.
        current_graph(plan, {debug_script: payload.decode("utf-8")})
        argv = coq_argv(backend, root, build, library.parent, script, debug=True)
        result = run_tool(argv, cwd=build, deadline=deadline, label="Rocq debug")
        return {**context, "status": "passed", "returncode": 0, "argv": argv, "cwd": str(build),
                "debug_script_path": str(script), "debug_script_size": len(payload),
                "load_argument": str(script), "resolved_script_path": str(script),
                "resolved_matches_authorized": True, "stdout_tail": tail(result.stdout),
                "stderr_tail": tail(result.stderr), "elapsed_seconds": round(time.monotonic() - started, 6)}
    except (CoqBuildPlanError, OSError, UnicodeError, ValueError) as exc:
        return failure_result(exc, started, **context)


def audit_formal_case_lib_closure(
    backend: Any, *, workspace_root: Path, build_workspace: Path,
    formal_case_lib: Path, current_case_anchor: Path,
) -> dict[str, Any]:
    started = time.monotonic()
    context = {"target_file": formal_case_lib.as_posix(), "compiled": False}
    try:
        root = workspace_root.expanduser().absolute()
        target = _repository_relative(formal_case_lib, root, label="case library")
        directory, name, family = _case_family(current_case_anchor)
        if target != directory / f"{name}_lib.v":
            raise ValueError("Library audit target differs from the current-case identity")
        plan = prepare_plan(backend, root=root, target=target, anchor=current_case_anchor,
                            deadline=command_deadline(None))
        forbidden = set(dependency_closure(plan_graph(plan), [target])) & (family - {target})
        if forbidden:
            raise ValueError(f"Case library depends on generated artifacts: {sorted(forbidden)}")
        return {**context, "status": "passed", "elapsed_seconds": round(time.monotonic() - started, 6)}
    except (CoqBuildPlanError, OSError, UnicodeError, ValueError) as exc:
        return failure_result(exc, started, **context)
