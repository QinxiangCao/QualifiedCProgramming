"""Native Dune dependency discovery/building; current proofs run in common."""

from __future__ import annotations

import errno
import os
import re
import shutil
import stat
import sys
import tempfile
import time
from collections.abc import Sequence
from pathlib import Path
from typing import Any, BinaryIO

from path_utils import fixed_path_under, path_is_link_like
from process_adapter import CONTROL_SIGNAL_ENV, ProcessCancelled, control_signal_requests_stop, tool_progress
from coq_tooling_common import (
    FIXED_LOAD_PATH_MAPPINGS, COQ_SIDE_PRODUCT_SUFFIXES, CoqBuildPlanError,
    dependency_closure, fixed_source, run_tool,
)

BUILD_MODE = "dune"
SOURCE_SIDE_PRODUCT_SUFFIXES = COQ_SIDE_PRODUCT_SUFFIXES + (".lia.cache", ".nia.cache", ".nra.cache")


def configured_program(root: Path, tool: str) -> str:
    variable = {"coqc": "COQC_EXE", "coqtop": "COQTOP_EXE", "dune": "DUNE_EXE"}[tool]
    if value := os.environ.get(variable, "").strip():
        return value
    if tool == "dune" and os.name == "nt" and (root / "dune.cmd").is_file():
        return str(root / "dune.cmd")
    return shutil.which(tool) or tool


def base_load_paths(root: Path) -> list[tuple[str, Path, str]]:
    base = fixed_path_under(root / "_build/default", root, label="Dune build root")
    return [(flag, fixed_path_under(base / physical, base, label="base load path"), logical)
            for flag, physical, logical in FIXED_LOAD_PATH_MAPPINGS]


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



def _acquire_dune_lock(root: Path, deadline: float) -> BinaryIO:
    """Serialize shared dependency refreshes; closing the handle releases the lock."""
    path = fixed_path_under(root / "_build" / ".qcp-dune.lock", root,
                            label="Dune dependency lock")
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = path.open("a+b")
    started = time.monotonic()
    progress = tool_progress(f"waiting for Dune dependency lock {path}")
    control = os.environ.get(CONTROL_SIGNAL_ENV)
    try:
        if os.name == "nt" and os.fstat(handle.fileno()).st_size == 0:
            handle.write(b"\0")
            handle.flush()
        waiting = False
        while True:
            if control and control_signal_requests_stop(Path(control)):
                raise ProcessCancelled("Dune dependency lock wait cancelled by controller request")
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"Timed out waiting for Dune dependency lock {path}")
            try:
                if os.name == "nt":
                    import msvcrt
                    handle.seek(0)
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                else:
                    import fcntl
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                return handle
            except OSError as exc:
                if exc.errno not in {errno.EACCES, errno.EAGAIN, errno.EDEADLK}:
                    raise
                if not waiting:
                    print(f"[QCP] waiting for Dune dependency lock {path}", file=sys.stderr, flush=True)
                    waiting = True
                progress(time.monotonic() - started, "", "")
                time.sleep(min(0.1, remaining))
    except BaseException:
        handle.close()
        raise



def _read_rules(root: Path, rules: Path) -> dict[Path, tuple[Path, ...]]:
    text = rules.read_text(encoding="utf-8").replace("\\\r\n", " ").replace("\\\n", " ")
    graph: dict[Path, set[Path]] = {}

    def source(token: str) -> Path | None:
        path = Path(_normalize_dune_dependency_token(token).replace("\\", "/"))
        path = path if path.is_absolute() else root / path
        try:
            relative = path.relative_to(root / "_build/default")
        except ValueError:
            return None
        return relative.with_suffix(".v") if relative.suffix == ".vo" and ".." not in relative.parts else None

    for line in text.splitlines():
        if line.startswith("\t") or ": " not in line:
            continue
        targets, dependencies = line.split(": ", 1)
        requires = {path for token in _dependency_words(dependencies) if (path := source(token)) is not None}
        for token in _dependency_words(targets):
            if (path := source(token)) is not None:
                graph.setdefault(path, set()).update(requires)
    return {path: tuple(sorted(dependencies)) for path, dependencies in graph.items()}


def prepare_native(
    *, root: Path, targets: Sequence[Path], family: set[Path], deadline: float,
) -> dict[Path, tuple[Path, ...]]:
    """Dune alone discovers dependencies and builds the non-current closure."""
    try:
        lock = _acquire_dune_lock(root, deadline)
    except TimeoutError as exc:
        raise CoqBuildPlanError(category="tooling", kind="dune-lock-timeout", message=str(exc),
                                repair="Wait for the shared Dune build, then retry.",
                                evidence={"returncode": 124}) from exc
    with lock, tempfile.TemporaryDirectory(prefix=".dune-rules-", dir=root) as temporary:
        rules = Path(temporary) / "rules.mk"
        dune = configured_program(root, "dune")
        run_tool([dune, "rules", "--recursive", "--makefile", "-o", str(rules),
                  "--root", str(root), *(path.with_suffix(".vo").as_posix() for path in targets)],
                 cwd=root, deadline=deadline, label="Dune dependency discovery")
        graph = _read_rules(root, rules)
        selected = dependency_closure(graph, targets)
        graph = {source: graph[source] for source in selected}
        base = set(graph) - family
        for source in selected:
            fixed_source(root, source)
            if source in base and set(graph[source]) & family:
                raise ValueError(f"Base module depends on the current case: {source}")
        if base:
            run_tool([dune, "build", "--root", str(root), "--display=short",
                      *(source.with_suffix(".vo").as_posix() for source in sorted(base))],
                     cwd=root, deadline=deadline, label="Dune base build")
        for source in base:
            fixed_source(root / "_build/default", source.with_suffix(".vo"), label="Dune base artifact")
        return graph
